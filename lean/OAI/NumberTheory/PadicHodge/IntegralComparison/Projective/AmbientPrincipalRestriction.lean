import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientChartRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AmbientLineBaseChange

/-! # Ambient Principal Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientPrincipalRestriction.Adjunction

noncomputable section

/-! Ambient projective adjunction after quotient scalar extension
commutes with literal restriction to a principal affine subopen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra AmbientAdjunction.sectionAlgebra

variable (i : Fin (n + 1)) (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (k : Fin (n + 1)) (hVk : AffinePrincipal.Sections.openSubset U r ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (j : Fin (n + 1))

local instance principalBaseTower :
    IsScalarTower R Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) :=
  IsScalarTower.of_algebraMap_eq (fun a =>
    (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (IntrinsicOverlap.Intrinsic.model R n)).map (AffinePrincipal.Sections.inclusion U r).op).hom.commutes a).symm)

theorem ambientIso_restriction
    (I : Ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (J : Ideal Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r))
    (hJ : I.map (algebraMap Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) = J)
    (hIJ : I ≤ J.comap (algebraMap Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)))
    (x : (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]
      (AffineOpen.InternalHom.sections U hU).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))) :
    letI : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
    LocalizedResidueRestriction.Conormal.exteriorRestrictionOfEq r I J hJ n
      (AmbientAdjunction.ambientIso i U hU hUi j I x) =
    AmbientAdjunction.ambientIso k (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) hVk j J
      (AffinePrincipal.LineFrame.lineMap U hU r
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) I J hIJ x) := by
  let : IsLocalization.Away r Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
  exact AmbientLineBaseChange.restriction r I J hJ hIJ
    ((AffineOpen.InternalHom.sections U hU).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)))
    ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)))
    (AffinePrincipal.LineFrame.restriction U hU r
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))) n
    (AmbientAdjunction.chartLineExterior i U hU hUi j)
    (AmbientAdjunction.chartLineExterior k (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) hVk j)
    (AmbientAdjunction.ambientIso i U hU hUi j I)
    (AmbientAdjunction.ambientIso k (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) hVk j J)
    (AmbientAdjunction.ambientIso_tmul i U hU hUi j I)
    (AmbientAdjunction.ambientIso_tmul k (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) hVk j J)
    (AmbientChartRestriction.Adjunction.chartLineExterior_restriction i U hU hUi r k hVk j) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientPrincipalRestriction.Adjunction
