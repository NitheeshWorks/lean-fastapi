import LeanFastapi.APIs
import LeanFastapi.Proofs.Verified

/-!
# LeanFastapi

A clean-room port of FastAPI to Lean 4: path operations declared with
`@[get "/items/{item_id}"]` on plain functions, parameter extraction with
pydantic's errors, response models and OpenAPI generation, each with its
contract proved.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call: the attributes, `FastAPI`, `TestClient`
-/
