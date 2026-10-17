import LeanFastapi.APIs
import LeanFastapi.Proofs.Verified

/-!
# LeanFastapi

A clean-room port of FastAPI to Lean 4: typed dependency injection, parameter extraction, response models and OpenAPI generation, each with its contract proved.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
