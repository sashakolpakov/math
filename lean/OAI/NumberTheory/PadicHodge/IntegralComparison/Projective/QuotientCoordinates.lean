import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue

/-! # Quotient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.QuotientCoordinates.LocalAdjunction

noncomputable section

/-! The projective adjunction and the principal residue use the
identical closed-immersion quotient on the affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)

omit [IsNoetherianRing R] in
theorem quotientSectionIso_eq_chart : LocalAdjunction.quotientSectionIso X f U hU =
    Closed.QuotientSectionNormalization.chartIso f.left U hU := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.QuotientCoordinates.LocalAdjunction
