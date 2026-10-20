"""Finite authored PostgreSQL context checks across session states.

This helper requires a connection whose current role is the authenticated
superuser. PostgreSQL requires that privilege to change session authorization;
DSN runs fail explicitly if it is absent. Two random NOLOGIN roles are created
inside one transaction and rolled back. A SQL error, timeout or disconnected
psql process also rolls that transaction back. No existing role is modified.

The original SELECT and its checked canonical rendering run in the same
states. The authenticated identity, database and external system identity are
setup premises, not inferred from SQL relation metadata. These finite native
observations do not prove general execution equivalence or fixed identities.
"""
from __future__ import annotations

import json
import uuid

from check_assurance_cli import assert_report
from check_pagination_cli import replay
from check_postgresql_cli import copy_result, marker, parse_results, run, sql_identifier, sql_literal


SOURCE = """SELECT CURRENT_SCHEMA AS schema_name,
current_schema() AS schema_call,
CURRENT_USER AS current_identity,
USER AS user_identity,
CURRENT_ROLE AS role_identity,
SESSION_USER AS session_identity,
CURRENT_CATALOG AS catalog_name,
current_database() AS database_name,
current_schemas(FALSE) AS explicit_schemas,
current_schemas(TRUE) AS implicit_schemas,
SYSTEM_USER AS system_identity;"""

COLUMNS = (
    ("schema_name", "name", True), ("schema_call", "name", True),
    ("current_identity", "name", False), ("user_identity", "name", False),
    ("role_identity", "name", False), ("session_identity", "name", False),
    ("catalog_name", "name", False), ("database_name", "name", False),
    ("explicit_schemas", "name[]", False), ("implicit_schemas", "name[]", False),
    ("system_identity", "text", True),
)
COUNTS = {
    "state_queries": 10, "state_values": 110,
    "static_queries": 2, "render_profiles": 2,
    "restoration_checks": 1, "role_cleanup_checks": 1,
}


def setup_identity(psql):
    query = """SELECT pg_catalog.json_build_object(
'current', CURRENT_USER, 'session', SESSION_USER,
'database', current_database(), 'system', SYSTEM_USER,
'superuser', (SELECT rolsuper FROM pg_catalog.pg_roles WHERE rolname=SESSION_USER))::text;"""
    output = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=query).stdout
    metadata = json.loads(output)
    assert isinstance(metadata, dict) and set(metadata) == {
        "current", "session", "database", "system", "superuser"}, metadata
    assert all(isinstance(metadata[key], str) and metadata[key] for key in
               ("current", "session", "database")), metadata
    assert metadata["system"] is None or isinstance(metadata["system"], str), metadata
    if metadata["superuser"] is not True or metadata["current"] != metadata["session"]:
        raise RuntimeError("Context session-state checks require the authenticated superuser "
                           "as the current role; cannot silently skip session authorization checks")
    return metadata


def state_script(metadata, canonical, role, session_role):
    """Build only authored statements; the role names are independently quoted."""
    assert role != session_role and role != metadata["session"] and session_role != metadata["session"]
    commands = [
        "BEGIN;", "SET LOCAL statement_timeout = '5s';", "SET LOCAL lock_timeout = '5s';",
        "SET LOCAL standard_conforming_strings = on;", "SET LOCAL client_min_messages = warning;",
        f"CREATE ROLE {sql_identifier(role)} NOLOGIN NOSUPERUSER NOCREATEDB NOCREATEROLE;",
        f"CREATE ROLE {sql_identifier(session_role)} NOLOGIN NOSUPERUSER NOCREATEDB NOCREATEROLE;",
    ]
    expected = {}

    def capture(index, setting, current, session, schema):
        commands.extend(setting)
        row = [schema, schema, current, current, current, session,
               metadata["database"], metadata["database"],
               "{}" if schema is None else "{pg_catalog}", "{pg_catalog}", metadata["system"]]
        for form, sql in (("source", SOURCE), ("postgres", canonical)):
            key = marker("context_session", index, True, form)
            commands.extend(["\\echo " + key, copy_result(sql)])
            expected[key] = (len(COLUMNS), [row.copy()])

    owner = metadata["session"]
    capture(1, ["SET LOCAL search_path = pg_catalog;"], owner, owner, "pg_catalog")
    capture(2, ["SET LOCAL search_path = '';"], owner, owner, None)
    capture(3, ["SET LOCAL search_path = pg_catalog;", f"SET LOCAL ROLE {sql_identifier(role)};"],
            role, owner, "pg_catalog")
    capture(4, ["SET LOCAL ROLE NONE;",
                f"SET LOCAL SESSION AUTHORIZATION {sql_identifier(session_role)};"],
            session_role, session_role, "pg_catalog")
    capture(5, ["SET LOCAL SESSION AUTHORIZATION DEFAULT;", "SET LOCAL ROLE NONE;"],
            owner, owner, "pg_catalog")
    commands.append("ROLLBACK;")
    key = marker("context_rollback", 1, True, "state")
    commands.extend(["\\echo " + key, copy_result(
        "SELECT CURRENT_USER = " + sql_literal(owner) +
        " AND SESSION_USER = " + sql_literal(owner) + " AS restored, "
        "NOT EXISTS (SELECT FROM pg_catalog.pg_roles WHERE rolname IN (" +
        sql_literal(role) + ", " + sql_literal(session_role) + ")) AS roles_absent;")])
    expected[key] = (2, [["t", "t"]])
    assert len(expected) == COUNTS["state_queries"] + 1
    return "\n".join(commands), expected


def check_states(psql):
    """Certify two query forms, execute ten state observations, verify cleanup."""
    metadata = setup_identity(psql)
    assert_report(["--assurance", "contract", SOURCE], "valid", "contract", COLUMNS)
    replay("identity", SOURCE)
    canonical = replay("postgres", SOURCE)["sql"]
    assert_report(["--assurance", "contract", canonical], "valid", "contract", COLUMNS)
    suffix = uuid.uuid4().hex
    script, expected = state_script(metadata, canonical,
                                    "sqlean_context_role_" + suffix,
                                    "sqlean_context_session_" + suffix)
    output = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=90).stdout
    actual = parse_results(output)
    assert actual.keys() == expected.keys(), ("missing or unexpected context state evidence",
                                              actual.keys(), expected.keys())
    for key, wanted in expected.items():
        assert actual[key] == wanted, (key, actual[key], wanted)
    return dict(COUNTS)
