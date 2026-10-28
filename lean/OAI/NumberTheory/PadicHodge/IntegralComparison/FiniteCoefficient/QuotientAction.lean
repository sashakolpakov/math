import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientAlgebra

/-! # Quotient Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.QuotientAction

noncomputable section

/-! The actual affine finite coefficient algebra is a module over the
literal normal-equation quotient, with the original ambient scalar action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable {Y X A : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ A) [IsClosedImmersion i]
  (U : A.Opens) (hU : IsAffineOpen U) {c : ℕ} (s : Fin c → Γ(A, U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(A, U) s = i.ker.ideal ⟨U,hU⟩)

include hs in
theorem normal_vanishes : KoszulPartial.Resolution.normalIdeal Γ(A, U) s ≤
    RingHom.ker (algebraMap Γ(A, U) (Finite.FlatCoefficientSections.quotientRing i U)) := by
  rw [hs, Scheme.Hom.ker_apply]
  exact le_rfl

@[instance_reducible]
def algebra : Algebra (Γ(A, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(A, U) s) (Finite.FlatCoefficientSections.coefficientRing f i U) :=
  IntegralComparison.Quotient.CoefficientAlgebra.algebra Γ(A, U) (Finite.FlatCoefficientSections.quotientRing i U)
    (Finite.FlatCoefficientSections.coefficientRing f i U) (KoszulPartial.Resolution.normalIdeal Γ(A, U) s) (normal_vanishes i U hU s hs)

theorem tower : letI := algebra f i U hU s hs
    IsScalarTower Γ(A, U) (Γ(A, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(A, U) s) (Finite.FlatCoefficientSections.coefficientRing f i U) :=
  IntegralComparison.Quotient.CoefficientAlgebra.tower Γ(A, U) (Finite.FlatCoefficientSections.quotientRing i U)
    (Finite.FlatCoefficientSections.coefficientRing f i U) (KoszulPartial.Resolution.normalIdeal Γ(A, U) s) (normal_vanishes i U hU s hs)

theorem algebraMap_mk (a : Γ(A, U)) : letI := algebra f i U hU s hs
    algebraMap (Γ(A, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(A, U) s) (Finite.FlatCoefficientSections.coefficientRing f i U)
      (Ideal.Quotient.mk _ a) = f.app (i ⁻¹ᵁ U) (i.app U a) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.QuotientAction
