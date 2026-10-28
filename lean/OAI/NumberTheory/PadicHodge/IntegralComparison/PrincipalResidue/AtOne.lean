import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization

/-! # At One -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AtOne.OrientedNormalization

noncomputable section

/-! Evaluation of the original principal residue on the unit open.
The closed coefficient identification retains the literal quotient map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization.sectionRing U
local notation "r₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne.object U

theorem residue_at_one
    (φ : (⋀[R]^c (Fin c → R)) →ₗ[R] Γ(Y, Principal.SectionPresheaf.openSubset U r₁))
    (x : R)
    (hφ : φ (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))) =
      algebraMap R Γ(Y, Principal.SectionPresheaf.openSubset U r₁) x) :
    (Principal.OrientedResidueNormalization.targetAtOne U hU f s hs).hom
      ((Koszul.CoefficientResidue.evaluation R (Principal.SectionPresheaf.rings U hU) s
        (Principal.ClosedKoszulResidue.target f U hU)
        (Principal.ClosedKoszulResidue.pullback f U hU s hs)).app (op r₁) φ) =
    Ideal.Quotient.mk (KoszulPartial.Resolution.normalIdeal R s) x := by
  rw [Principal.ClosedKoszulResidue.evaluation, hφ]
  exact Principal.OrientedResidueNormalization.targetAtOne_pullback U hU f s hs x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AtOne.OrientedNormalization
