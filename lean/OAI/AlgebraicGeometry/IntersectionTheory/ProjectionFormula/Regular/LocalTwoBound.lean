import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalTwoParameters
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.LocalDimension
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Local Two Bound -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalTwoBound

noncomputable section

/-! The actual residue field of a two-dimensional regular local domain
has projective dimension at most two, using its regular pair of parameters. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing
open scoped Pointwise TensorProduct

universe u

variable (R : Type u) [CommRing R]

theorem quotient_bound (M : ModuleCat.{u} R) (r : R) (hr : IsSMulRegular M r)
    (d : ℕ) [HasProjectiveDimensionLE M d] :
    HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop r M)) (d + 1) := by
  have hS := IsSMulRegular.smulShortComplex_shortExact (M := M) hr
  exact hS.hasProjectiveDimensionLT_X₃ (d + 1)
    (inferInstanceAs (HasProjectiveDimensionLT M (d + 1)))
    (hasProjectiveDimensionLT_of_ge M (d + 1) (d + 2) (by omega))

def quotientPairEquiv (a b : R) :
    QuotSMulTop b (R ⧸ Ideal.span {a}) ≃ₗ[R] R ⧸ Ideal.span {a, b} := by
  let S := R ⧸ Ideal.span {a}
  let e := LinearEquiv.restrictScalars R
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {b})).symm.toLinearEquiv
  exact (QuotSMulTop.equivTensorQuot b S).trans
    (e.trans
        ((DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {a}) (Ideal.span {b})).toLinearEquiv.trans
          (Ideal.quotientEquivAlgOfEq R (by
            rw [← Ideal.span_union]
            rfl)).toLinearEquiv))

theorem residue_bound [IsRegularLocalRing R] [IsDomain R] (hd : ringKrullDim R = 2) :
    HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) 2 := by
  obtain ⟨a, b, ha, hm, hb⟩ := LocalTwoParameters.exists_pair R hd
  have hI : (a • (⊤ : Submodule R R) : Ideal R) = Ideal.span {a} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e₁ : QuotSMulTop a R ≃ₗ[R] (R ⧸ Ideal.span {a}) := Submodule.quotEquivOfEq _ _ hI
  let : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop a R)) 1 :=
    quotient_bound R (ModuleCat.of R R) a (fun _ _ h => mul_left_cancel₀ ha h) 0
  let : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.span {a})) 1 :=
    hasProjectiveDimensionLT_of_iso e₁.toModuleIso 2
  let : HasProjectiveDimensionLE
      (ModuleCat.of R (QuotSMulTop b (R ⧸ Ideal.span {a}))) 2 :=
    quotient_bound R (ModuleCat.of R (R ⧸ Ideal.span {a})) b hb 1
  let e := (quotientPairEquiv R a b).trans (Ideal.quotientEquivAlgOfEq R hm.symm).toLinearEquiv
  exact hasProjectiveDimensionLT_of_iso e.toModuleIso 3

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalTwoBound
