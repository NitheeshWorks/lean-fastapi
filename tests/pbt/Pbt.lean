import LeanFastapi
import Plausible

/-!
# Plausible properties

Randomised checks run at build time with `plausible` (`#eval
Testable.check`, which fails the build on a counter-example), on plausible's
own generators: the name and path helpers and the `json.loads` recogniser,
which are tested rather than proved.
-/

namespace Pbt

open LeanFastapi

-- `json.loads` error positions never point past the text.
#eval Plausible.Testable.check (∀ s : String,
  (match PyJson.checkText s.toList.toArray with
   | some (.decode _ pos) => decide (pos ≤ s.length)
   | _ => true) = true)

-- A JSON string literal of any text (escaped by lean-json) is accepted.
#eval Plausible.Testable.check (∀ s : String,
  (PyJson.checkText (LeanJson.printStr (.str s)).toList.toArray).isNone = true)

#eval Plausible.Testable.check (∀ s : String, snakeCase (snakeCase s) = snakeCase s)

#eval Plausible.Testable.check (∀ s : String, pathFormat (pathFormat s) = pathFormat s)

#eval Plausible.Testable.check (∀ s : String, (headerAlias s).length = s.length)

#eval Plausible.Testable.check (∀ (n p : String),
  (generateUniqueId n p "get").toList.all isWordChar = true)


-- Cookie names come out unique, whatever the header.
#eval Plausible.Testable.check (∀ s : String,
  let keys := (cookieParser s).map (·.1)
  keys.eraseDups.length = keys.length)

end Pbt
