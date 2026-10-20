import SQLean.PostgresGrammar.Generated.Symbols
import SQLean.PostgresGrammar.Generated.Productions000
import SQLean.PostgresGrammar.Generated.Productions001
import SQLean.PostgresGrammar.Generated.Productions002
import SQLean.PostgresGrammar.Generated.Productions003
import SQLean.PostgresGrammar.Generated.Productions004
import SQLean.PostgresGrammar.Generated.Productions005
import SQLean.PostgresGrammar.Generated.Productions006
import SQLean.PostgresGrammar.Generated.Productions007
import SQLean.PostgresGrammar.Generated.Productions008
import SQLean.PostgresGrammar.Generated.Productions009
import SQLean.PostgresGrammar.Generated.Productions010
import SQLean.PostgresGrammar.Generated.Productions011
import SQLean.PostgresGrammar.Generated.Productions012
import SQLean.PostgresGrammar.Generated.Productions013
import SQLean.PostgresGrammar.Generated.Productions014
import SQLean.PostgresGrammar.Generated.Productions015
import SQLean.PostgresGrammar.Generated.Productions016
import SQLean.PostgresGrammar.Generated.Productions017
import SQLean.PostgresGrammar.Generated.Productions018
import SQLean.PostgresGrammar.Generated.Productions019
import SQLean.PostgresGrammar.Generated.Productions020
import SQLean.PostgresGrammar.Generated.Productions021
import SQLean.PostgresGrammar.Generated.Productions022
import SQLean.PostgresGrammar.Generated.Productions023
import SQLean.PostgresGrammar.Generated.Productions024
import SQLean.PostgresGrammar.Generated.Productions025
import SQLean.PostgresGrammar.Generated.Shifts000
import SQLean.PostgresGrammar.Generated.Shifts001
import SQLean.PostgresGrammar.Generated.Shifts002
import SQLean.PostgresGrammar.Generated.Shifts003
import SQLean.PostgresGrammar.Generated.Shifts004
import SQLean.PostgresGrammar.Generated.Shifts005
import SQLean.PostgresGrammar.Generated.Shifts006
import SQLean.PostgresGrammar.Generated.Shifts007
import SQLean.PostgresGrammar.Generated.Shifts008
import SQLean.PostgresGrammar.Generated.Shifts009
import SQLean.PostgresGrammar.Generated.Shifts010
import SQLean.PostgresGrammar.Generated.Shifts011
import SQLean.PostgresGrammar.Generated.Shifts012
import SQLean.PostgresGrammar.Generated.Shifts013
import SQLean.PostgresGrammar.Generated.Shifts014
import SQLean.PostgresGrammar.Generated.Shifts015
import SQLean.PostgresGrammar.Generated.Shifts016
import SQLean.PostgresGrammar.Generated.Shifts017
import SQLean.PostgresGrammar.Generated.Shifts018
import SQLean.PostgresGrammar.Generated.Shifts019
import SQLean.PostgresGrammar.Generated.Shifts020
import SQLean.PostgresGrammar.Generated.Shifts021
import SQLean.PostgresGrammar.Generated.Shifts022
import SQLean.PostgresGrammar.Generated.Shifts023
import SQLean.PostgresGrammar.Generated.Shifts024
import SQLean.PostgresGrammar.Generated.Shifts025
import SQLean.PostgresGrammar.Generated.Shifts026
import SQLean.PostgresGrammar.Generated.Shifts027
import SQLean.PostgresGrammar.Generated.Shifts028
import SQLean.PostgresGrammar.Generated.States000
import SQLean.PostgresGrammar.Generated.States001
import SQLean.PostgresGrammar.Generated.States002
import SQLean.PostgresGrammar.Generated.States003
import SQLean.PostgresGrammar.Generated.States004
import SQLean.PostgresGrammar.Generated.States005
import SQLean.PostgresGrammar.Generated.States006
import SQLean.PostgresGrammar.Generated.States007
import SQLean.PostgresGrammar.Generated.States008
import SQLean.PostgresGrammar.Generated.States009
import SQLean.PostgresGrammar.Generated.States010
import SQLean.PostgresGrammar.Generated.States011
import SQLean.PostgresGrammar.Generated.States012
import SQLean.PostgresGrammar.Generated.States013
import SQLean.PostgresGrammar.Generated.States014
import SQLean.PostgresGrammar.Generated.States015
import SQLean.PostgresGrammar.Generated.States016
import SQLean.PostgresGrammar.Generated.States017
import SQLean.PostgresGrammar.Generated.States018
import SQLean.PostgresGrammar.Generated.States019
import SQLean.PostgresGrammar.Generated.States020
import SQLean.PostgresGrammar.Generated.States021
import SQLean.PostgresGrammar.Generated.States022
import SQLean.PostgresGrammar.Generated.States023
import SQLean.PostgresGrammar.Generated.States024

/-! Generated from PostgreSQL 16.15 at f0595c3d839debdb140903621c1b44a4f4d86256.
Regenerate with scripts/generate_postgresql_grammar.py; no upstream C actions execute. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace SQLean.PostgresGrammar.Generated

def grammar : Grammar := {
  productions := productions000 ++ productions001 ++ productions002 ++ productions003 ++ productions004 ++ productions005 ++ productions006 ++ productions007 ++ productions008 ++ productions009 ++ productions010 ++ productions011 ++ productions012 ++ productions013 ++ productions014 ++ productions015 ++ productions016 ++ productions017 ++ productions018 ++ productions019 ++ productions020 ++ productions021 ++ productions022 ++ productions023 ++ productions024 ++ productions025
  startSymbol := 520
  terminalKinds := terminals.map TerminalInfo.symbol
  eofKind := eofKind }

def tables : Tables := {
  shiftRows := shifts000 ++ shifts001 ++ shifts002 ++ shifts003 ++ shifts004 ++ shifts005 ++ shifts006 ++ shifts007 ++ shifts008 ++ shifts009 ++ shifts010 ++ shifts011 ++ shifts012 ++ shifts013 ++ shifts014 ++ shifts015 ++ shifts016 ++ shifts017 ++ shifts018 ++ shifts019 ++ shifts020 ++ shifts021 ++ shifts022 ++ shifts023 ++ shifts024 ++ shifts025 ++ shifts026 ++ shifts027 ++ shifts028
  states := states000 ++ states001 ++ states002 ++ states003 ++ states004 ++ states005 ++ states006 ++ states007 ++ states008 ++ states009 ++ states010 ++ states011 ++ states012 ++ states013 ++ states014 ++ states015 ++ states016 ++ states017 ++ states018 ++ states019 ++ states020 ++ states021 ++ states022 ++ states023 ++ states024
  initialState := 0 }

end SQLean.PostgresGrammar.Generated
