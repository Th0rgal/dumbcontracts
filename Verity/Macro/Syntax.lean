import Lean

namespace Verity.Macro

open Lean

declare_syntax_cat verityStorageField
declare_syntax_cat verityParam
declare_syntax_cat verityConstructor
declare_syntax_cat verityFunction

syntax ident " : " term " := " "slot" num : verityStorageField
syntax ident " : " term : verityParam
syntax "constructor " "(" sepBy(verityParam, ",") ")" " := " term : verityConstructor
syntax "function " ident " (" sepBy(verityParam, ",") ")" " : " term " := " term : verityFunction

syntax (name := verityContractCmd)
  "verity_contract " ident " where "
  "storage " verityStorageField+
  (verityConstructor)?
  verityFunction+ : command

end Verity.Macro
