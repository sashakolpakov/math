import OAI.AlgebraicTopology.Kunneth.TensorSimplicialForms
import OAI.AlgebraicTopology.Kunneth.RestrictedWedgeNaturality
import OAI.AlgebraicTopology.Kunneth.RestrictedSimplexIntegration

/-! # Simplex Wedge Integral -/

namespace OAI.AlgebraicTopology.Kunneth.SimplexWedgeIntegral

noncomputable section

/-! Wedge integration as a functional on the exact tensor model. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct Simplicial

namespace Constructions

def simplexTensorWedge (q n p : ℕ) :
    TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) (q + p) :=
  (RestrictedWedge.Constructions.restrictedFormDegreeCast (SimplexFormDomain.Constructions.coordinateSimplex n) (Nat.add_comm p q)).toLinearMap.comp
    ((TensorProduct.lift (RestrictedWedge.Constructions.restrictedWedge (SimplexFormDomain.Constructions.coordinateSimplex n) p q)).comp
      (TensorProduct.map LinearMap.id (SimplicialForms.Constructions.SimplexClosedForms n q).subtype))

@[simp] theorem simplexTensorWedge_tmul (q n p : ℕ)
    (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) p) (b : SimplicialForms.Constructions.SimplexClosedForms n q) :
    simplexTensorWedge q n p (a ⊗ₜ[ℂ] b) =
      RestrictedWedge.Constructions.restrictedFormDegreeCast (SimplexFormDomain.Constructions.coordinateSimplex n) (Nat.add_comm p q)
        (RestrictedWedge.Constructions.restrictedWedge (SimplexFormDomain.Constructions.coordinateSimplex n) p q a b.val) := rfl

theorem simplexTensorWedge_d (q n p : ℕ) (a : TensorSimplicialForms.Constructions.SimplexFormTensor q n p) :
    RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) (q + p) (simplexTensorWedge q n p a) =
      simplexTensorWedge q n (p + 1) (TensorSimplicialForms.Constructions.simplexFormTensorD q n p a) := by
  have h : (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) (q + p)).comp
        (simplexTensorWedge q n p) =
      (simplexTensorWedge q n (p + 1)).comp (TensorSimplicialForms.Constructions.simplexFormTensorD q n p) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) (q + p)
      (RestrictedWedge.Constructions.restrictedFormDegreeCast (SimplexFormDomain.Constructions.coordinateSimplex n) (Nat.add_comm p q)
        (RestrictedWedge.Constructions.restrictedWedge (SimplexFormDomain.Constructions.coordinateSimplex n) p q x y.val)) =
      RestrictedWedge.Constructions.restrictedFormDegreeCast (SimplexFormDomain.Constructions.coordinateSimplex n) (Nat.add_comm (p + 1) q)
        (RestrictedWedge.Constructions.restrictedWedge (SimplexFormDomain.Constructions.coordinateSimplex n) (p + 1) q
          (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) p x) y.val)
    rw [RestrictedWedgeNaturality.Constructions.restrictedFormDegreeCast_d,
      RestrictedWedge.Constructions.restrictedWedge_d_of_right_closed (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) x y.val y.property,
      RestrictedWedgeNaturality.Constructions.restrictedFormDegreeCast_trans]
    rfl
  exact LinearMap.congr_fun h a

theorem simplexTensorWedge_pullback {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) (q p : ℕ) (a : TensorSimplicialForms.Constructions.SimplexFormTensor q n p) :
    SimplexFormMaps.Constructions.simplexFormPullback f (q + p) (simplexTensorWedge q n p a) =
      simplexTensorWedge q m p (TensorSimplicialForms.Constructions.simplexFormTensorPullback f q p a) := by
  have h : (SimplexFormMaps.Constructions.simplexFormPullback f (q + p)).comp (simplexTensorWedge q n p) =
      (simplexTensorWedge q m p).comp (TensorSimplicialForms.Constructions.simplexFormTensorPullback f q p) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change SimplexFormMaps.Constructions.simplexFormPullback f (q + p)
      (RestrictedWedge.Constructions.restrictedFormDegreeCast (SimplexFormDomain.Constructions.coordinateSimplex n) (Nat.add_comm p q)
        (RestrictedWedge.Constructions.restrictedWedge (SimplexFormDomain.Constructions.coordinateSimplex n) p q x y.val)) =
      RestrictedWedge.Constructions.restrictedFormDegreeCast (SimplexFormDomain.Constructions.coordinateSimplex m) (Nat.add_comm p q)
        (RestrictedWedge.Constructions.restrictedWedge (SimplexFormDomain.Constructions.coordinateSimplex m) p q
          (SimplexFormMaps.Constructions.simplexFormPullback f p x) (SimplexFormMaps.Constructions.simplexFormPullback f q y.val))
    unfold SimplexFormMaps.Constructions.simplexFormPullback
    rw [RestrictedWedgeNaturality.Constructions.restrictedFormDegreeCast_pullback, RestrictedWedgeNaturality.Constructions.restrictedWedge_pullback]
  exact LinearMap.congr_fun h a

def simplexWedgeIntegral (q p : ℕ) : TensorSimplicialForms.Constructions.SimplexFormTensor q (q + p) p →ₗ[ℂ] ℂ :=
  (RestrictedSimplexIntegration.Constructions.simplexIntegral (q + p)).comp (simplexTensorWedge q (q + p) p)

theorem simplexWedgeIntegral_d (q p : ℕ) :
    (simplexWedgeIntegral q (p + 1)).comp (TensorSimplicialForms.Constructions.simplexFormTensorD q (q + p + 1) p) =
      TensorSimplicialForms.Constructions.simplexFormTensorDelta q (q + p) p (simplexWedgeIntegral q p) := by
  apply LinearMap.ext
  intro a
  change RestrictedSimplexIntegration.Constructions.simplexIntegral (q + p + 1)
    (simplexTensorWedge q (q + p + 1) (p + 1) (TensorSimplicialForms.Constructions.simplexFormTensorD q (q + p + 1) p a)) = _
  rw [← simplexTensorWedge_d, RestrictedSimplexIntegration.Constructions.simplexIntegral_stokes, TensorSimplicialForms.Constructions.simplexFormTensorDelta_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [simplexTensorWedge_pullback]
  rfl

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.SimplexWedgeIntegral
