import LeanFastapi.Specifications.FastAPI
import LeanFastapi.Proofs.Params
import LeanFastapi.Proofs.OpenApi
import LeanFastapi.Proofs.Security
import LeanFastapi.Proofs.Dependencies

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` bundles a proof term for every headline property of
`Specifications/FastAPI.lean` that layer claims. A property with no proof is
a compile error the moment it needs a field here: a `Verified<Layer>` value
cannot be built without every proof in hand. Properties that are tested
rather than proved have no slot; they are listed in `CONTRIBUTING.md` and
`docs/traceability.toml`.
-/

namespace LeanFastapi

/-- Parameters, extraction, the 422 response and response models. -/
structure VerifiedRequests : Prop where
  paramsToArgsLoc : Spec.ParamsToArgsLoc
  extractSound : Spec.ExtractSound
  extractConsOkIff : Spec.ExtractConsOkIff
  extract422 : Spec.Extract422
  inferParam : Spec.InferParam
  headerAliasHyphen : Spec.HeaderAliasHyphen
  serializeResponseConforms : Spec.SerializeResponseConforms
  embedRule : Spec.EmbedRule
  embedBodies : Spec.EmbedBodies
  formExtractLoc : Spec.FormExtractLoc

theorem theVerifiedRequests : VerifiedRequests where
  paramsToArgsLoc := params_to_args_loc
  extractSound := extract_sound
  extractConsOkIff := extract_cons_ok_iff
  extract422 := extract_422
  inferParam := infer_param
  headerAliasHyphen := header_alias_hyphen
  serializeResponseConforms := serialize_response_conforms
  embedRule := embed_rule
  embedBodies fs := ⟨embedBodies_embed fs, shouldEmbed_embedBodies fs⟩
  formExtractLoc p inp fs hs he hb :=
    ⟨fun es h => form_field_loc p inp es hs he h, fun hr hd => form_missing p inp fs hs he hb hr hd⟩

/-- The OpenAPI document, for every application. -/
structure VerifiedOpenapi : Prop where
  allRoutes : Spec.OpenapiAllRoutes
  refsResolve : Spec.OpenapiRefsResolve
  componentsSorted : Spec.OpenapiComponentsSorted
  operationIdUnique : Spec.OperationIdUnique
  operationOfRoute : Spec.OpenapiOperationOfRoute
  validation422Iff : Spec.Openapi422Iff
  paramsMatch : Spec.OpenapiParamsMatch

theorem theVerifiedOpenapi : VerifiedOpenapi where
  allRoutes app := openapi_all_routes app.info app.routes
  refsResolve app := openapi_refs_resolve app.info app.routes
  componentsSorted app := openapi_components_sorted app.info app.routes
  operationIdUnique app := operationId_unique app.info app.routes
  operationOfRoute app := openapi_operation_of_route app.info app.routes
  validation422Iff := openapi_422_iff
  paramsMatch := openapi_params_match

/-- Solving dependencies: order, cache, overrides, exit stacks, scopes. -/
structure VerifiedDependencies : Prop where
  solveOrder : Spec.SolveOrder
  paramsErrors : Spec.ParamsErrors
  cacheSameKey : Spec.CacheSameKey
  cachedStores : Spec.CachedStores
  overrideReplaces : Spec.OverrideReplaces
  cleanupReverse : Spec.CleanupReverse
  functionScopeNotOutlive : Spec.FunctionScopeNotOutlive
  securityScopesAccumulate : Spec.SecurityScopesAccumulate
  mergeScopesMem : Spec.MergeScopesMem

theorem theVerifiedDependencies : VerifiedDependencies where
  solveOrder := solve_order
  paramsErrors := params_errors
  cacheSameKey := cache_same_key
  cachedStores := cached_stores
  overrideReplaces := override_replaces
  cleanupReverse := cleanup_reverse
  functionScopeNotOutlive := function_scope_not_outlive
  securityScopesAccumulate := security_scopes_accumulate
  mergeScopesMem := mergeScopes_mem

/-- The security schemes. -/
structure VerifiedSecurity : Prop where
  bearerParse : Spec.BearerParse
  basicBase64Roundtrip : Spec.BasicBase64Roundtrip
  apikeySources : Spec.ApikeySources

theorem theVerifiedSecurity : VerifiedSecurity where
  bearerParse := bearer_parse
  basicBase64Roundtrip := basic_base64_roundtrip
  apikeySources := apikey_sources

end LeanFastapi
