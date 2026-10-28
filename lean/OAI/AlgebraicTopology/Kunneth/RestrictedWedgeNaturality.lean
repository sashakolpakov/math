import OAI.AlgebraicTopology.Kunneth.RestrictedWedge
import OAI.AlgebraicTopology.Kunneth.RestrictedFormsZero

/-! # Restricted Wedge Naturality -/

namespace OAI.AlgebraicTopology.Kunneth.RestrictedWedgeNaturality

noncomputable section

/-! Naturality and the degree-zero normalization of the actual restricted wedge. -/

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace Constructions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p q : ℕ}

local instance wedgeNaturalFormsAddGroup (n : ℕ) : AddCommGroup (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance
local instance wedgeNaturalFormsModule (n : ℕ) : Module ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance

theorem normedWedge_pullback (f : E → F) (hf : ContDiff ℝ ∞ f)
    (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm F p) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm F q) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf (WedgeAlgebra.Constructions.normedWedge a b) =
      WedgeAlgebra.Constructions.normedWedge (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf a) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf b) := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  exact (CovectorWedge.Constructions.covectorWedge_pullback (fderiv ℝ f x) (a (f x)) (b (f x))).symm

theorem restrictedWedge_pullback {S : Set E} {T : Set F}
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hmap : MapsTo f S T)
    (a : RestrictedForms.Constructions.RestrictedForm T p) (b : RestrictedForms.Constructions.RestrictedForm T q) :
    RestrictedFormPullback.Constructions.restrictedFormPullback f hf hmap (p + q) (RestrictedWedge.Constructions.restrictedWedge T p q a b) =
      RestrictedWedge.Constructions.restrictedWedge S p q (RestrictedFormPullback.Constructions.restrictedFormPullback f hf hmap p a)
        (RestrictedFormPullback.Constructions.restrictedFormPullback f hf hmap q b) := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn T p).mkQ_surjective a
  obtain ⟨b, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn T q).mkQ_surjective b
  change RestrictedForms.Constructions.restrictForm S (p + q) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf (WedgeAlgebra.Constructions.normedWedge a b)) =
    RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedge (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf a) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf b))
  rw [normedWedge_pullback]

theorem restrictedFormDegreeCast_trans (S : Set E) {n m k : ℕ} (h : n = m) (h' : m = k)
    (a : RestrictedForms.Constructions.RestrictedForm S n) :
    RestrictedWedge.Constructions.restrictedFormDegreeCast S h' (RestrictedWedge.Constructions.restrictedFormDegreeCast S h a) =
      RestrictedWedge.Constructions.restrictedFormDegreeCast S (h.trans h') a := by
  subst m k
  rfl

theorem restrictedFormDegreeCast_d {S : Set E} (hS : UniqueDiffOn ℝ S)
    {n m : ℕ} (h : n = m) (a : RestrictedForms.Constructions.RestrictedForm S n) :
    RestrictedForms.Constructions.restrictedFormD hS m (RestrictedWedge.Constructions.restrictedFormDegreeCast S h a) =
      RestrictedWedge.Constructions.restrictedFormDegreeCast S (congrArg (· + 1) h) (RestrictedForms.Constructions.restrictedFormD hS n a) := by
  subst m
  rfl

theorem restrictedFormDegreeCast_pullback {S : Set E} {T : Set F}
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hmap : MapsTo f S T)
    {n m : ℕ} (h : n = m) (a : RestrictedForms.Constructions.RestrictedForm T n) :
    RestrictedFormPullback.Constructions.restrictedFormPullback f hf hmap m (RestrictedWedge.Constructions.restrictedFormDegreeCast T h a) =
      RestrictedWedge.Constructions.restrictedFormDegreeCast S h (RestrictedFormPullback.Constructions.restrictedFormPullback f hf hmap n a) := by
  subst m
  rfl

theorem covectorWedge_degree_zero (a : E [⋀^Fin 0]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    CovectorWedge.Constructions.covectorDegreeCast (Nat.zero_add q) (CovectorWedge.Constructions.covectorWedge a b) = (a 0) • b := by
  ext v
  rw [CovectorWedge.Constructions.covectorDegreeCast_apply, FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum, ← FinAlternatingProduct.Constructions.alternatingSum_cast]
  have he : (fun w : Fin q → E => FinAlternatingProduct.Constructions.finBlockProduct a b
      (fun i => w (Fin.cast (Nat.zero_add q) i))) = fun w => a 0 * b w := by
    funext w
    unfold FinAlternatingProduct.Constructions.finBlockProduct
    congr 1
    · congr 1
      exact Subsingleton.elim _ _
    · congr 1
      funext i
      exact congrArg w (Fin.ext (by simp))
  rw [he, WedgeAlternating.Constructions.alternatingSum_smul, WedgeAlternating.Constructions.alternatingSum_of_alternating]
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Fintype.card_fin,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, nsmul_eq_mul,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hq : (q.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
  field_simp

theorem normedWedge_constantZeroForm (c : ℂ) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q) :
    WedgeAlgebra.Constructions.normedFormDegreeCast (Nat.zero_add q) (WedgeAlgebra.Constructions.normedWedge (RestrictedFormsZero.Constructions.constantZeroForm c) b) = c • b := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  rw [WedgeAlgebra.Constructions.normedFormDegreeCast_apply, WedgeAlgebra.Constructions.normedWedge_apply, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.smul_apply]
  exact covectorWedge_degree_zero (RestrictedFormsZero.Constructions.constantZeroForm c x) (b x)

theorem restrictedWedge_constantZeroForm (S : Set E) (c : ℂ) (b : RestrictedForms.Constructions.RestrictedForm S q) :
    RestrictedWedge.Constructions.restrictedFormDegreeCast S (Nat.zero_add q)
      (RestrictedWedge.Constructions.restrictedWedge S 0 q (RestrictedForms.Constructions.restrictForm S 0 (RestrictedFormsZero.Constructions.constantZeroForm c)) b) = c • b := by
  obtain ⟨b, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S q).mkQ_surjective b
  change RestrictedWedge.Constructions.restrictedFormDegreeCast S (Nat.zero_add q)
    (RestrictedForms.Constructions.restrictForm S (0 + q) (WedgeAlgebra.Constructions.normedWedge (RestrictedFormsZero.Constructions.constantZeroForm c) b)) =
      c • RestrictedForms.Constructions.restrictForm S q b
  rw [RestrictedWedge.Constructions.restrictedFormDegreeCast_restrict, normedWedge_constantZeroForm]
  exact (RestrictedForms.Constructions.restrictForm S q).map_smul c b

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.RestrictedWedgeNaturality
