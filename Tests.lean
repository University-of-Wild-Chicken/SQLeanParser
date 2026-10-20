import Tests.Parsing
import Tests.Validation
import Tests.Corpus
import Tests.Proofs
import Tests.CrudParsing
import Tests.CrudValidation
import Tests.CrudCorpus
import Tests.CrudAPI
import Tests.RelationalParsing
import Tests.RelationalValidation
import Tests.NestedValidation
import Tests.RelationalCorpus
import Tests.IndustrialParsing
import Tests.IndustrialValidation
import Tests.IndustrialCorpus
import Tests.IndustrialAPI
import Tests.PostgresParsing
import Tests.PostgresValidation
import Tests.PostgresReturning
import Tests.PostgresCorpus
import Tests.AdvancedParsing
import Tests.AdvancedValidation
import Tests.AdvancedStatements
import Tests.AdvancedCorpus
import Tests.SelectContract
import Tests.SelectContractTrust
import Tests.ScopeContract
import Tests.ScopeContractTrust
import Tests.RenderContract
import Tests.DialectRendering
import Tests.PaginationRendering
import Tests.PaginationCorpus
import Tests.ExtendedTypeRendering
import Tests.ExtendedTypeCorpus
import Tests.PostgresGrammar
import Tests.PostgresLexer
import Tests.ScalarFormCorpus
import Tests.LockingRendering
import Tests.LockingContract
import Tests.ParserDispatch
import Tests.JoinContract
import Tests.JoinPreservation
import Tests.MergedJoinPreservation
import Tests.MergedJoinContract
import Tests.DerivedContract
import Tests.DerivedPreservation
import Tests.ArrayTypeContract
import Tests.ArrayTypeRendering
import Tests.ArrayConstructorContract
import Tests.ArrayConstructorRendering
import Tests.ArrayQuantifiedContract
import Tests.ArrayQuantifiedRendering
import Tests.ArraySubscriptContract
import Tests.ArraySubscriptRendering
import Tests.RowComparisonContract
import Tests.RowComparisonRendering
import Tests.ConcatenationContract
import Tests.ConcatenationRendering
import Tests.PatternMatchingContract
import Tests.PatternMatchingRendering
import Tests.JsonExtractionContract
import Tests.JsonExtractionRendering
import Tests.JsonContainmentContract
import Tests.JsonContainmentRendering
import Tests.ArrayConcatenationContract
import Tests.ArrayConcatenationRendering
import Tests.ArrayPredicateContract
import Tests.ArrayPredicateRendering
import Tests.ExtractContract
import Tests.ExtractRendering
import Tests.IntervalFieldsContract
import Tests.IntervalFieldsRendering
import Tests.SubstringContract
import Tests.SubstringRendering
import Tests.QualifiedNamesContract
import Tests.QualifiedNamesRendering
import Tests.JsonExistenceContract
import Tests.JsonExistenceRendering
import Tests.ContextValuesContract
import Tests.ContextValuesRendering
import Tests.NamedArgumentsContract
import Tests.NamedArgumentsRendering
import Tests.KeywordFunctionsContract
import Tests.KeywordFunctionsRendering
import Tests.NullPredicatesContract
import Tests.NullPredicatesRendering

namespace SQLean.Tests

def run : IO Unit := do
  let parsing ← parsingTests
  IO.println s!"PASS: {parsing} parser acceptance/rejection, AST, round-trip, and position cases"
  let validation ← validationTests
  IO.println s!"PASS: {validation} schema/type/API cases"
  let corpus ← corpusTests
  IO.println s!"PASS: {corpus} distinct generated queries parsed, certified, and round-tripped"
  let crudParsing ← crudParsingTests
  IO.println s!"PASS: {crudParsing} CRUD parser and compatibility cases"
  let crudValidation ← crudValidationTests
  IO.println s!"PASS: {crudValidation} CRUD schema/type and certificate cases"
  let crudAPI ← crudAPITests
  IO.println s!"PASS: {crudAPI} CRUD public API cases"
  let crudCorpus ← crudCorpusTests
  IO.println s!"PASS: {crudCorpus} new CRUD examples (50 per category) parsed, certified, and round-tripped"
  let relationalParsing ← relationalParsingTests
  IO.println s!"PASS: {relationalParsing} relational parser and round-trip cases"
  let relationalValidation ← relationalValidationTests
  IO.println s!"PASS: {relationalValidation} join/group/type validity cases"
  let nested ← nestedValidationTests
  IO.println s!"PASS: {nested} nested query scope and certificate cases"
  let relationalCorpus ← relationalCorpusTests
  IO.println s!"PASS: {relationalCorpus} relational examples (50 per query class) certified and round-tripped"
  let industrialParsing ← industrialParsingTests
  IO.println s!"PASS: {industrialParsing} recursive CTE, UNION, and source-free parsing cases"
  let industrialValidation ← industrialValidationTests
  IO.println s!"PASS: {industrialValidation} recursive scope, compound type, and certificate cases"
  let industrialCorpus ← industrialCorpusTests
  IO.println s!"PASS: {industrialCorpus} industrial examples (50 per query class) certified and round-tripped"
  let industrialAPI ← industrialAPITests
  IO.println s!"PASS: {industrialAPI} industrial public API cases"
  let postgresParsing ← postgresParsingTests
  IO.println s!"PASS: {postgresParsing} PostgreSQL syntax, precedence, and AST round-trip checks"
  let postgresValidation ← postgresValidationTests
  IO.println s!"PASS: {postgresValidation} PostgreSQL type, grouping, and option validity checks"
  let postgresReturning ← postgresReturningTests
  IO.println s!"PASS: {postgresReturning} RETURNING mutation, projection, and API checks"
  let postgresCorpus ← postgresCorpusTests
  IO.println s!"PASS: {postgresCorpus} PostgreSQL examples (50 per feature class) certified and round-tripped"
  let advancedParsing ← advancedParsingTests
  IO.println s!"PASS: {advancedParsing} advanced parser, parameter identity, and round-trip checks"
  let advancedValidation ← advancedValidationTests
  IO.println s!"PASS: {advancedValidation} advanced query scope, type, and parameter checks"
  let advancedStatements ← advancedStatementTests
  IO.println s!"PASS: {advancedStatements} advanced mutation, DDL, catalog, and API checks"
  let advancedCorpus ← advancedCorpusTests
  IO.println s!"PASS: {advancedCorpus} advanced examples (50 per query class) certified and round-tripped"
  let contract ← selectContractTests
  IO.println s!"PASS: {contract} independent SELECT contract and assurance API checks"
  let render ← renderContractTests
  IO.println s!"PASS: {render} SELECT rendering, exact round-trip, binding-map, and corpus checks"
  let dialect ← dialectRenderingTests
  IO.println s!"PASS: {dialect} SQLite and PostgreSQL dialect rendering checks"
  let paginationRender ← paginationRenderingTests
  IO.println s!"PASS: {paginationRender} pagination rendering and parameter boundary checks"
  let paginationCorpus ← paginationCorpusTests
  IO.println s!"PASS: {paginationCorpus} synthetic/full-query and concrete/bounds-only pagination certificates"
  let extendedTypes ← extendedTypeRenderingTests
  IO.println s!"PASS: {extendedTypes} extended type syntax and rendering checks"
  let extendedTypeCorpus ← extendedTypeCorpusTests
  IO.println s!"PASS: {extendedTypeCorpus} exact-type synthetic SELECT certificates and rendering checks"
  let scalarForms ← scalarFormCorpusTests
  IO.println s!"PASS: {scalarForms} function/conditional full SELECT certificates and rendering checks"
  let scalarBoundaries ← scalarFormBoundaryTests
  IO.println s!"PASS: {scalarBoundaries} scalar signatures, parameter order, and syntax boundaries"
  let dispatch ← parserDispatchTests
  IO.println s!"PASS: {dispatch} default-parser special-form dispatch checks"
  let lockingRender ← lockingRenderingTests
  IO.println s!"PASS: {lockingRender} row-locking rendering and parameter-order checks"
  let lockingContract ← lockingContractTests
  IO.println s!"PASS: {lockingContract} row-locking validity and scope boundary checks"
  let lockingCorpus ← lockingCorpusTests
  IO.println s!"PASS: {lockingCorpus} row-locking full-query and renderer certificates"
  let joinContract ← joinContractTests
  IO.println s!"PASS: {joinContract} independent JOIN scope, nullability, and parameter checks"
  let joinCorpus ← joinCorpusTests
  IO.println s!"PASS: {joinCorpus} JOIN full-query and renderer certificates"
  let mergedJoinContract ← mergedJoinContractTests
  IO.println s!"PASS: {mergedJoinContract} USING/NATURAL namespace, type, and output-order checks"
  let usingCorpus ← usingCorpusTests
  IO.println s!"PASS: {usingCorpus} USING full-query and renderer certificates"
  let naturalCorpus ← naturalCorpusTests
  IO.println s!"PASS: {naturalCorpus} NATURAL full-query and renderer certificates"
  let derivedContract ← derivedContractTests
  IO.println s!"PASS: {derivedContract} nested derived-source scope and parameter checks"
  let derivedCorpus ← derivedCorpusTests
  IO.println s!"PASS: {derivedCorpus} derived-source full-query and renderer certificates"
  let arrayTypeContract ← arrayTypeContractTests
  IO.println s!"PASS: {arrayTypeContract} exact array type and parameter modifier checks"
  let arrayTypeCorpus ← arrayTypeCorpusTests
  IO.println s!"PASS: {arrayTypeCorpus} array type full-query and renderer certificates"
  let arrayTypeRendering ← arrayTypeRenderingTests
  IO.println s!"PASS: {arrayTypeRendering} array type parsing and rendering checks"
  let arrayConstructorContract ← arrayConstructorContractTests
  IO.println s!"PASS: {arrayConstructorContract} ARRAY construction validity and context checks"
  let arrayConstructorCorpus ← arrayConstructorCorpusTests
  IO.println s!"PASS: {arrayConstructorCorpus} ARRAY constructor full-query certificates"
  let arrayConstructorRendering ← arrayConstructorRenderingTests
  IO.println s!"PASS: {arrayConstructorRendering} ARRAY constructor parsing and rendering checks"
  let arrayQuantifiedContract ← arrayQuantifiedContractTests
  IO.println s!"PASS: {arrayQuantifiedContract} quantified array validity and operator checks"
  let arrayQuantifiedCorpus ← arrayQuantifiedCorpusTests
  IO.println s!"PASS: {arrayQuantifiedCorpus} quantified array full-query certificates"
  let arrayQuantifiedRendering ← arrayQuantifiedRenderingTests
  IO.println s!"PASS: {arrayQuantifiedRendering} quantified array parsing and rendering checks"
  let arraySubscriptContract ← arraySubscriptContractTests
  IO.println s!"PASS: {arraySubscriptContract} array subscript/slice validity and label checks"
  let arraySubscriptCorpus ← arraySubscriptCorpusTests
  IO.println s!"PASS: {arraySubscriptCorpus} array subscript/slice full-query certificates"
  let arraySubscriptRendering ← arraySubscriptRenderingTests
  IO.println s!"PASS: {arraySubscriptRendering} array subscript/slice parsing and rendering checks"
  let rowComparisonContract ← rowComparisonContractTests
  IO.println s!"PASS: {rowComparisonContract} row comparison validity and operator checks"
  let rowComparisonCorpus ← rowComparisonCorpusTests
  IO.println s!"PASS: {rowComparisonCorpus} row comparison full-query certificates"
  let rowComparisonRendering ← rowComparisonRenderingTests
  IO.println s!"PASS: {rowComparisonRendering} row comparison parsing and rendering checks"
  let concatenationContract ← concatenationContractTests
  IO.println s!"PASS: {concatenationContract} concatenation validity and operator checks"
  let concatenationCorpus ← concatenationCorpusTests
  IO.println s!"PASS: {concatenationCorpus} concatenation full-query certificates"
  let concatenationRendering ← concatenationRenderingTests
  IO.println s!"PASS: {concatenationRendering} concatenation parsing and rendering checks"
  let patternMatchingContract ← patternMatchingContractTests
  IO.println s!"PASS: {patternMatchingContract} pattern matching validity and operator checks"
  let patternMatchingCorpus ← patternMatchingCorpusTests
  IO.println s!"PASS: {patternMatchingCorpus} pattern matching full-query certificates"
  let patternMatchingRendering ← patternMatchingRenderingTests
  IO.println s!"PASS: {patternMatchingRendering} pattern matching parsing and rendering checks"
  let jsonExtractionContract ← jsonExtractionContractTests
  IO.println s!"PASS: {jsonExtractionContract} JSON extraction validity and operator checks"
  let jsonExtractionCorpus ← jsonExtractionCorpusTests
  IO.println s!"PASS: {jsonExtractionCorpus} JSON extraction full-query certificates"
  let jsonExtractionConcrete ← jsonExtractionConcreteContractTests
  IO.println s!"PASS: {jsonExtractionConcrete} unchanged JSON extraction source certificates"
  let jsonExtractionRendering ← jsonExtractionRenderingTests
  IO.println s!"PASS: {jsonExtractionRendering} JSON extraction parsing and rendering checks"
  let jsonContainmentContract ← jsonContainmentContractTests
  IO.println s!"PASS: {jsonContainmentContract} JSONB containment validity and operator checks"
  let jsonContainmentCorpus ← jsonContainmentCorpusTests
  IO.println s!"PASS: {jsonContainmentCorpus} JSONB containment full-query certificates"
  let jsonContainmentConcrete ← jsonContainmentConcreteContractTests
  IO.println s!"PASS: {jsonContainmentConcrete} unchanged JSONB containment source certificates"
  let jsonContainmentRendering ← jsonContainmentRenderingTests
  IO.println s!"PASS: {jsonContainmentRendering} JSONB containment parsing and rendering checks"
  let arrayConcatenationContract ← arrayConcatenationContractTests
  IO.println s!"PASS: {arrayConcatenationContract} array concatenation validity and operator checks"
  let arrayConcatenationCorpus ← arrayConcatenationCorpusTests
  IO.println s!"PASS: {arrayConcatenationCorpus} array concatenation full-query certificates"
  let arrayConcatenationConcrete ← arrayConcatenationConcreteContractTests
  IO.println s!"PASS: {arrayConcatenationConcrete} unchanged array concatenation source certificates"
  let arrayConcatenationRendering ← arrayConcatenationRenderingTests
  IO.println s!"PASS: {arrayConcatenationRendering} array concatenation rendering checks"
  let arrayPredicateContract ← arrayPredicateContractTests
  IO.println s!"PASS: {arrayPredicateContract} array predicate validity and operator checks"
  let arrayPredicateCorpus ← arrayPredicateCorpusTests
  IO.println s!"PASS: {arrayPredicateCorpus} array predicate full-query certificates"
  let arrayPredicateConcrete ← arrayPredicateConcreteContractTests
  IO.println s!"PASS: {arrayPredicateConcrete} unchanged array predicate source certificates"
  let arrayPredicateRendering ← arrayPredicateRenderingTests
  IO.println s!"PASS: {arrayPredicateRendering} array predicate parsing and rendering checks"
  let extractContract ← extractContractTests
  IO.println s!"PASS: {extractContract} EXTRACT validity and signature checks"
  let extractCorpus ← extractCorpusTests
  IO.println s!"PASS: {extractCorpus} EXTRACT full-query certificates"
  let extractConcrete ← extractConcreteContractTests
  IO.println s!"PASS: {extractConcrete} unchanged EXTRACT source certificates"
  let extractRendering ← extractRenderingTests
  IO.println s!"PASS: {extractRendering} EXTRACT parsing and rendering checks"
  let intervalFieldsContract ← intervalFieldsContractTests
  IO.println s!"PASS: {intervalFieldsContract} interval field modifier and signature checks"
  let intervalFieldsCorpus ← intervalFieldsCorpusTests
  IO.println s!"PASS: {intervalFieldsCorpus} interval field full-query certificates"
  let intervalFieldsConcrete ← intervalFieldsConcreteContractTests
  IO.println s!"PASS: {intervalFieldsConcrete} unchanged interval field source certificates"
  let intervalFieldsRendering ← intervalFieldsRenderingTests
  IO.println s!"PASS: {intervalFieldsRendering} interval field parsing and rendering checks"
  let substringContract ← substringContractTests
  IO.println s!"PASS: {substringContract} SUBSTRING validity and signature checks"
  let substringCorpus ← substringCorpusTests
  IO.println s!"PASS: {substringCorpus} SUBSTRING full-query certificates"
  let substringConcrete ← substringConcreteContractTests
  IO.println s!"PASS: {substringConcrete} unchanged SUBSTRING source certificates"
  let substringRendering ← substringRenderingTests
  IO.println s!"PASS: {substringRendering} SUBSTRING parsing and rendering checks"
  let qualifiedNamesContract ← qualifiedNamesContractTests
  IO.println s!"PASS: {qualifiedNamesContract} qualified relation namespace checks"
  let qualifiedNamesCorpus ← qualifiedNamesCorpusTests
  IO.println s!"PASS: {qualifiedNamesCorpus} qualified relation full-query certificates"
  let qualifiedNamesConcrete ← qualifiedNamesConcreteRenderingTests
  IO.println s!"PASS: {qualifiedNamesConcrete} unchanged qualified source rendering certificates"
  let qualifiedNamesRendering ← qualifiedNamesRenderingTests
  IO.println s!"PASS: {qualifiedNamesRendering} qualified relation parsing and rendering checks"
  let jsonExistenceContract ← jsonExistenceContractTests
  IO.println s!"PASS: {jsonExistenceContract} JSONB existence validity and signature checks"
  let jsonExistenceCorpus ← jsonExistenceCorpusTests
  IO.println s!"PASS: {jsonExistenceCorpus} JSONB existence full-query certificates"
  let jsonExistenceConcrete ← jsonExistenceConcreteContractTests
  IO.println s!"PASS: {jsonExistenceConcrete} unchanged JSONB existence full-query certificates (all 50 rendered)"
  let jsonExistenceRendering ← jsonExistenceRenderingTests
  IO.println s!"PASS: {jsonExistenceRendering} JSONB existence parsing and rendering checks"
  let contextValuesContract ← contextValuesContractTests
  IO.println s!"PASS: {contextValuesContract} context values and NAME signature checks"
  let contextValuesCorpus ← contextValuesCorpusTests
  IO.println s!"PASS: {contextValuesCorpus} context-value full-query certificates"
  let contextValuesConcrete ← contextValuesConcreteContractTests
  IO.println s!"PASS: {contextValuesConcrete} unchanged context-value full-query certificates (all 50 rendered)"
  let contextValuesRendering ← contextValuesRenderingTests
  IO.println s!"PASS: {contextValuesRendering} context-value parsing and rendering checks"
  let namedArgumentsContract ← namedArgumentsContractTests
  IO.println s!"PASS: {namedArgumentsContract} named argument binding and default checks"
  let namedArgumentsCorpus ← namedArgumentsCorpusTests
  IO.println s!"PASS: {namedArgumentsCorpus} named/default call full-query certificates"
  let namedArgumentsConcrete ← namedArgumentsConcreteContractTests
  IO.println s!"PASS: {namedArgumentsConcrete} unchanged named-call full-query certificates (all 50 rendered)"
  let namedArgumentsRendering ← namedArgumentsRenderingTests
  IO.println s!"PASS: {namedArgumentsRendering} named-call parsing and rendering checks"
  let keywordFunctionsContract ← keywordFunctionsContractTests
  IO.println s!"PASS: {keywordFunctionsContract} keyword function signature and coercion checks"
  let keywordFunctionsCorpus ← keywordFunctionsCorpusTests
  IO.println s!"PASS: {keywordFunctionsCorpus} keyword function full-query certificates"
  let keywordFunctionsConcrete ← keywordFunctionsConcreteContractTests
  IO.println s!"PASS: {keywordFunctionsConcrete} unchanged keyword function certificates (all 50 rendered)"
  let keywordFunctionsRendering ← keywordFunctionsRenderingTests
  IO.println s!"PASS: {keywordFunctionsRendering} keyword function parsing and rendering checks"
  let nullPredicatesContract ← nullPredicatesContractTests
  IO.println s!"PASS: {nullPredicatesContract} NULL-aware scalar/row predicate checks"
  let nullPredicatesCorpus ← nullPredicatesCorpusTests
  IO.println s!"PASS: {nullPredicatesCorpus} NULL predicate full-query certificates"
  let nullPredicatesConcrete ← nullPredicatesConcreteContractTests
  IO.println s!"PASS: {nullPredicatesConcrete} unchanged NULL predicate certificates (all 100 rendered)"
  let nullPredicatesRendering ← nullPredicatesRenderingTests
  IO.println s!"PASS: {nullPredicatesRendering} NULL predicate parsing and rendering checks"
  let pgLexical ← postgresLexerTests
  IO.println s!"PASS: {pgLexical} PostgreSQL lexer and exact-source checks"
  let pgGrammar ← postgresGrammarTests
  IO.println s!"PASS: {pgGrammar} PostgreSQL grammar derivations and parser boundary checks"
  ScopeContract.run
  IO.println "All tests passed. Lean proof examples compiled successfully."

end SQLean.Tests
