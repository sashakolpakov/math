import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.PeriodFieldAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodActionLieRanks

/-! # Field Eigenspaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FieldEigenspaces.IntrinsicNumberFieldAction

noncomputable section

/-! The full number-field eigenspaces on the native tangent space are
the eigenspaces of the original integral action. Their dimensions come
from the actual dual-number Lie rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodActionLieRanks.IntrinsicIntegralAction

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def complexFieldEigenspace (σ : E →ₐ[ℚ] ℂ) : Submodule ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) where
  carrier := {v | ∀ a : E, PeriodFieldAction.IntrinsicNumberFieldAction.complexFieldAction A P ρ a v = σ a • v}
  zero_mem' a := by rw [map_zero, smul_zero]
  add_mem' hu hv a := by rw [map_add, hu a, hv a, smul_add]
  smul_mem' z v hv a := by rw [map_smul, hv a, smul_comm]

theorem complexFieldEigenspace_eq_integral (σ : E →ₐ[ℚ] ℂ) :
    complexFieldEigenspace A P ρ σ = PeriodActionLieRanks.IntrinsicIntegralAction.periodActionEigenspace A P ρ
      (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) := by
  ext v
  constructor
  · intro hv b
    exact (LinearMap.congr_fun (PeriodFieldAction.IntrinsicNumberFieldAction.complexFieldAction_integer A P ρ b) v).symm.trans (hv (b : E))
  · intro hv a
    let V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)
    let F : E →ₗ[ℚ] V := (LinearMap.applyₗ' ℚ v).comp (PeriodFieldAction.IntrinsicNumberFieldAction.complexFieldAction A P ρ).toLinearMap
    let G : E →ₗ[ℚ] V := (((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight v).restrictScalars ℚ).comp σ.toLinearMap
    have hi (b : NumberField.RingOfIntegers E) : F (b : E) = G (b : E) :=
      (LinearMap.congr_fun (PeriodFieldAction.IntrinsicNumberFieldAction.complexFieldAction_integer A P ρ b) v).trans (hv b)
    exact LinearMap.congr_fun (Integral.RosatiExtension.rationalLinearMap_eq_of_integers (E := E) (W := V) F G hi) a

theorem complexFieldEigenspace_finrank (σ : E →ₐ[ℚ] ℂ) {r : ℕ}
    (hr : LieRanks.HasLieRank A ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r) :
    Module.finrank ℂ (complexFieldEigenspace A P ρ σ) = r := by
  rw [complexFieldEigenspace_eq_integral]
  exact PeriodActionLieRanks.IntrinsicIntegralAction.periodActionEigenspace_finrank A P ρ _ hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FieldEigenspaces.IntrinsicNumberFieldAction
