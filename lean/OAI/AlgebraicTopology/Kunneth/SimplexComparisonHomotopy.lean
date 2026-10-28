import OAI.AlgebraicTopology.Kunneth.SimplexWedgeIntegral
import OAI.AlgebraicTopology.Kunneth.SimplexCupIntegral
import OAI.AlgebraicTopology.Products.Cup
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation

/-! # Simplex Comparison Homotopy -/

namespace OAI.AlgebraicTopology.Kunneth.SimplexComparisonHomotopy

noncomputable section

section

/-! The integration products agree on the degree-zero kernel, including after tensoring. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite OAI.AlgebraicTopology.Products.Cup
open scoped Simplicial TensorProduct ContDiff

namespace Constructions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance comparisonZeroFormsAddGroup (n : ℕ) : AddCommGroup (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance
local instance comparisonZeroFormsModule (n : ℕ) : Module ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance

theorem constantZeroForm_d (c : ℂ) : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (RestrictedFormsZero.Constructions.constantZeroForm (E := E) c) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  ext v
  change Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const c).toZeroForm x v = 0
  rw [Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply]
  change fderiv ℝ (fun _ : E => c) x (v 0) = 0
  rw [fderiv_const_apply]
  rfl

theorem constantZeroForm_pullback (f : E → F) (hf : ContDiff ℝ ∞ f) (c : ℂ) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf (RestrictedFormsZero.Constructions.constantZeroForm c) = RestrictedFormsZero.Constructions.constantZeroForm c := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  ext v
  rfl

def constantRestrictedForm (n : ℕ) : ℂ →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) 0 where
  toFun c := RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex n) 0 (RestrictedFormsZero.Constructions.constantZeroForm c)
  map_add' c c' := by
    rw [← map_add]
    congr 1
  map_smul' c c' := by
    rw [← map_smul]
    congr 1

@[simp] theorem constantRestrictedForm_apply (n : ℕ) (c : ℂ) :
    constantRestrictedForm n c = RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex n) 0 (RestrictedFormsZero.Constructions.constantZeroForm c) := rfl

theorem constantRestrictedForm_exact (n : ℕ) :
    Function.Exact (constantRestrictedForm n) (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) 0) := by
  intro a
  constructor
  · intro ha
    obtain ⟨c, hc⟩ := RestrictedFormsZero.Constructions.restrictedFormD_zero_constant (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n)
      (SimplexFormDomain.Constructions.coordinateSimplex_convex n) (SimplexFormDomain.Constructions.coordinateSimplex_zero n) a ha
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    rw [constantRestrictedForm_apply, RestrictedForms.Constructions.restrictedFormD_restrict, constantZeroForm_d, map_zero]

theorem simplexFormPullback_constant {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) (c : ℂ) :
    SimplexFormMaps.Constructions.simplexFormPullback f 0 (constantRestrictedForm n c) = constantRestrictedForm m c := by
  change RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex m) 0
    (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback (SimplexFormMaps.Constructions.simplexCoordinateMap f) _ (RestrictedFormsZero.Constructions.constantZeroForm c)) =
      RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex m) 0 (RestrictedFormsZero.Constructions.constantZeroForm c)
  rw [constantZeroForm_pullback]

theorem simplexIntegral_zero_constant (c : ℂ) : RestrictedSimplexIntegration.Constructions.simplexIntegral 0 (constantRestrictedForm 0 c) = c := by
  change DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (RestrictedSimplexIntegration.Constructions.coordinateIdentitySimplex 0)
    (RestrictedFormsZero.Constructions.constantZeroForm c).toManifold = c
  rw [DeRham.Comparison.SmoothSimplexAugmentation.smoothSimplexIntegration_zero]
  rfl

theorem simplexFormCochain_constant (n : ℕ) (c : ℂ) :
    SimplexFormCochain.Constructions.simplexFormCochain n 0 (constantRestrictedForm n c) = c • Products.Cup.cupUnit Δ[n] := by
  apply Products.Cup.cochain_ext Δ[n] (ModuleCat.of ℂ ℂ)
  intro s
  rw [SimplexFormCochain.Constructions.simplexFormCochain_evaluation, simplexFormPullback_constant, simplexIntegral_zero_constant,
    map_smul, Products.Cup.evaluation_cupUnit]
  exact (mul_one c).symm

theorem simplexWedgeIntegral_constant (q : ℕ) (c : ℂ) (b : SimplicialForms.Constructions.SimplexClosedForms q q) :
    SimplexWedgeIntegral.Constructions.simplexWedgeIntegral q 0 (constantRestrictedForm q c ⊗ₜ[ℂ] b) = c * RestrictedSimplexIntegration.Constructions.simplexIntegral q b.val := by
  change RestrictedSimplexIntegration.Constructions.simplexIntegral q (RestrictedWedge.Constructions.restrictedFormDegreeCast (SimplexFormDomain.Constructions.coordinateSimplex q) (Nat.zero_add q)
    (RestrictedWedge.Constructions.restrictedWedge (SimplexFormDomain.Constructions.coordinateSimplex q) 0 q
      (RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex q) 0 (RestrictedFormsZero.Constructions.constantZeroForm c)) b.val)) = _
  rw [RestrictedWedgeNaturality.Constructions.restrictedWedge_constantZeroForm, map_smul]
  rfl

theorem simplexCupIntegral_constant (q : ℕ) (c : ℂ) (b : SimplicialForms.Constructions.SimplexClosedForms q q) :
    SimplexCupIntegral.Constructions.simplexCupIntegral q 0 (constantRestrictedForm q c ⊗ₜ[ℂ] b) = c * RestrictedSimplexIntegration.Constructions.simplexIntegral q b.val := by
  change Cohomology.Singular.Coefficients.simplicialEvaluation Δ[q] (ModuleCat.of ℂ ℂ) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q⦌))
    (SimplexCupIntegral.Constructions.simplexTensorCup q q 0 (constantRestrictedForm q c ⊗ₜ[ℂ] b)) = _
  rw [SimplexCupIntegral.Constructions.simplexTensorCup_tmul, simplexFormCochain_constant, Products.Cup.cupWith_smul_left, map_smul]
  change Cohomology.Singular.Coefficients.simplicialEvaluation Δ[q] (ModuleCat.of ℂ ℂ) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q⦌))
    (c • Products.Cup.cochainCast Δ[q] (ModuleCat.of ℂ ℂ) (Nat.zero_add q)
      (Products.Cup.cup Δ[q] (Products.Cup.cupUnit Δ[q]) (SimplexFormCochain.Constructions.simplexFormCochain q q b.val))) = _
  rw [Products.Cup.cupUnit_cup, map_smul, SimplexFormCochain.Constructions.simplexFormCochain_evaluation]
  change c * RestrictedSimplexIntegration.Constructions.simplexIntegral q (SimplexFormMaps.Constructions.simplexFormPullback (id : Fin (q + 1) → Fin (q + 1)) q b.val) = _
  rw [SimplexFormMaps.Constructions.simplexFormPullback_id]

theorem simplexIntegral_difference_zero_kernel (q : ℕ) :
    LinearMap.ker (TensorSimplicialForms.Constructions.simplexFormTensorD q q 0) ≤
      LinearMap.ker (SimplexWedgeIntegral.Constructions.simplexWedgeIntegral q 0 - SimplexCupIntegral.Constructions.simplexCupIntegral q 0) := by
  let c := (constantRestrictedForm q).rTensor ↥(SimplicialForms.Constructions.SimplexClosedForms q q)
  have hex : Function.Exact c (TensorSimplicialForms.Constructions.simplexFormTensorD q q 0) :=
    Module.Flat.rTensor_exact ↥(SimplicialForms.Constructions.SimplexClosedForms q q) (constantRestrictedForm_exact q)
  have hz : (SimplexWedgeIntegral.Constructions.simplexWedgeIntegral q 0 - SimplexCupIntegral.Constructions.simplexCupIntegral q 0).comp c = 0 := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro b
    change SimplexWedgeIntegral.Constructions.simplexWedgeIntegral q 0 (constantRestrictedForm q z ⊗ₜ[ℂ] b) -
      SimplexCupIntegral.Constructions.simplexCupIntegral q 0 (constantRestrictedForm q z ⊗ₜ[ℂ] b) = 0
    rw [simplexWedgeIntegral_constant, simplexCupIntegral_constant, sub_self]
  intro a ha
  obtain ⟨b, rfl⟩ := (hex a).mp ha
  exact LinearMap.congr_fun hz b

end Constructions

end

/-! An unconditional homotopy between genuine wedge integration and cup integration. -/

set_option backward.isDefEq.respectTransparency false

namespace Constructions

def simplexIntegrationDifference (q p : ℕ) : TensorSimplicialForms.Constructions.SimplexFormTensor q (q + p) p →ₗ[ℂ] ℂ :=
  SimplexWedgeIntegral.Constructions.simplexWedgeIntegral q p - SimplexCupIntegral.Constructions.simplexCupIntegral q p

theorem simplexIntegrationDifference_d (q p : ℕ) :
    (simplexIntegrationDifference q (p + 1)).comp (TensorSimplicialForms.Constructions.simplexFormTensorD q (q + p + 1) p) =
      TensorSimplicialForms.Constructions.simplexFormTensorDelta q (q + p) p (simplexIntegrationDifference q p) := by
  rw [simplexIntegrationDifference, LinearMap.sub_comp, SimplexWedgeIntegral.Constructions.simplexWedgeIntegral_d,
    SimplexCupIntegral.Constructions.simplexCupIntegral_d, ← map_sub]
  rfl

theorem exists_simplexComparisonHomotopy (q : ℕ) :
    ∃ H : ∀ p, TensorSimplicialForms.Constructions.SimplexFormTensor q (q + p) (p + 1) →ₗ[ℂ] ℂ,
      (H 0).comp (TensorSimplicialForms.Constructions.simplexFormTensorD q q 0) = simplexIntegrationDifference q 0 ∧
      ∀ p, (H (p + 1)).comp (TensorSimplicialForms.Constructions.simplexFormTensorD q (q + p + 1) (p + 1)) =
        simplexIntegrationDifference q (p + 1) - TensorSimplicialForms.Constructions.simplexFormTensorDelta q (q + p) (p + 1) (H p) := by
  let : ∀ n p, AddCommGroup (TensorSimplicialForms.Constructions.SimplexFormTensor q n p) := fun n p => inferInstance
  let : ∀ n p, Module ℂ (TensorSimplicialForms.Constructions.SimplexFormTensor q n p) := fun n p => inferInstance
  refine CochainModelHomotopy.Constructions.modelFunctionalHomotopy (K := ℂ) (TensorSimplicialForms.Constructions.SimplexFormTensor q)
    (TensorSimplicialForms.Constructions.simplexFormTensorD q) (TensorSimplicialForms.Constructions.simplexFormTensorDelta q) ?_ ?_ ?_
    q (simplexIntegrationDifference q) ?_ ?_
  · exact TensorSimplicialForms.Constructions.simplexFormTensorD_exact q
  · exact TensorSimplicialForms.Constructions.simplexFormTensorDelta_d q
  · exact TensorSimplicialForms.Constructions.simplexFormTensorDelta_squared q
  · exact simplexIntegrationDifference_d q
  · exact simplexIntegral_difference_zero_kernel q

def simplexComparisonHomotopy (q p : ℕ) : TensorSimplicialForms.Constructions.SimplexFormTensor q (q + p) (p + 1) →ₗ[ℂ] ℂ :=
  (exists_simplexComparisonHomotopy q).choose p

theorem simplexComparisonHomotopy_zero (q : ℕ) (a : TensorSimplicialForms.Constructions.SimplexFormTensor q q 0) :
    simplexComparisonHomotopy q 0 (TensorSimplicialForms.Constructions.simplexFormTensorD q q 0 a) = simplexIntegrationDifference q 0 a :=
  LinearMap.congr_fun (exists_simplexComparisonHomotopy q).choose_spec.1 a

theorem simplexComparisonHomotopy_succ (q p : ℕ) (a : TensorSimplicialForms.Constructions.SimplexFormTensor q (q + p + 1) (p + 1)) :
    simplexComparisonHomotopy q (p + 1) (TensorSimplicialForms.Constructions.simplexFormTensorD q (q + p + 1) (p + 1) a) =
      simplexIntegrationDifference q (p + 1) a -
        TensorSimplicialForms.Constructions.simplexFormTensorDelta q (q + p) (p + 1) (simplexComparisonHomotopy q p) a :=
  LinearMap.congr_fun ((exists_simplexComparisonHomotopy q).choose_spec.2 p) a

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.SimplexComparisonHomotopy
