import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LineFrame

/-! # Ambient Chart Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientChartRestriction.Adjunction

noncomputable section

/-! The ambient top-form comparison commutes with the literal
restriction of affine chart sections used by oriented purity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra AmbientAdjunction.sectionAlgebra

variable (i : Fin (n + 1)) (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (k : Fin (n + 1)) (hVk : AffinePrincipal.Sections.openSubset U r ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (j : Fin (n + 1))

theorem chartLineExterior_restriction
    (x : (AffineOpen.InternalHom.sections U hU).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))) :
    AmbientAdjunction.chartLineExterior k (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) hVk j
        (AffinePrincipal.LineFrame.restriction U hU r
          (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) x) =
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap
        ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (IntrinsicOverlap.Intrinsic.model R n)).map (AffinePrincipal.Sections.inclusion U r).op) n
          (AmbientAdjunction.chartLineExterior i U hU hUi j x) := by
  change AmbientAdjunction.lineExterior k (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) hVk j
    ((Affine.ChartSections.iso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))).inv
        ((Affine.ChartSections.iso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
          (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))).hom
            ((AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)).presheaf.map (AffinePrincipal.Sections.inclusion U r).op
              ((Affine.ChartSections.iso U hU
                (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))).inv x)))) = _
  rw [Iso.hom_inv_id_apply]
  exact AmbientNormalization.Adjunction.lineExterior_restriction i U hU hUi k (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) hVk
    (AffinePrincipal.Sections.inclusion U r) j _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientChartRestriction.Adjunction
