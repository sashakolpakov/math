import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionPullbackZero
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.DetectionByFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedFlatIdeals
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction

/-! # Configuration Determines Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.ConfigurationDeterminesIdeal

noncomputable section

/-! Detecting families of actual scheme morphisms determine the
homogeneous relation module of a saturated ideal. Uniform Hilbert
reconstruction then determines the whole ideal over nonreduced bases. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction.GradedHilbert
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n d : ℕ}

theorem coordinateQuotientActualTwistingSection_eq_zero_iff
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :
    Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d q = 0 ↔ q = 0 := by
  let e := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv
    (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf
  change e.symm (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q) = 0 ↔ q = 0
  constructor
  · intro h
    have hq : SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q = 0 :=
      (e.apply_symm_apply _).symm.trans ((congrArg e h).trans (map_zero e))
    exact (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap_injective I hI d)
      (hq.trans (map_zero _).symm)
  · rintro rfl
    exact (congrArg e.symm (map_zero (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d))).trans
      (map_zero e.symm)

theorem homogeneousPolynomial_mem_iff_detectingFamily
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    {S : Scheme.{u}} {ι : Type v} (x : ι → (S ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
    (hx : Section.DetectionByFamilies.SectionsDetectedBy (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d) x) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) :
    p.val ∈ I ↔ ∀ c, Ample.LineBundles.pullbackSection (x c)
      (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) = 0 := by
  constructor
  · intro hp c
    have hq : (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hp
    rw [(coordinateQuotientActualTwistingSection_eq_zero_iff I hI _).mpr hq]
    exact (BasisPullbackSectionSurjectivity.pullbackSectionAddHom (x c) (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).map_zero
  · intro hp
    change p ∈ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d
    exact (Submodule.Quotient.mk_eq_zero (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d)).mp
      ((coordinateQuotientActualTwistingSection_eq_zero_iff I hI _).mp (hx _ hp))

theorem degreeRelations_eq_of_detectingFamilies
    (I J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (hJ : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
    {S : Scheme.{u}} {ι : Type v}
    (x : ι → (S ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (y : ι → (S ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)))
    (hx : Section.DetectionByFamilies.SectionsDetectedBy (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d) x)
    (hy : Section.DetectionByFamilies.SectionsDetectedBy (ProjectiveTwisting.Bundle.projectiveTwistingBundle J d) y)
    (hxy : ∀ c, x c ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = y c ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d := by
  ext p
  change p.val ∈ I ↔ p.val ∈ J
  rw [homogeneousPolynomial_mem_iff_detectingFamily I hI x hx,
    homogeneousPolynomial_mem_iff_detectingFamily J hJ y hy]
  apply forall_congr'
  intro c
  exact HilbertConstruction.Polynomial.SectionPullbackZero.polynomialSection_pullback_zero_iff_of_ambient_eq I p (x c) J (y c) (hxy c)

theorem saturatedHilbertIdeal_eq_of_detectingFamilyConfiguration
    [IsNoetherianRing R] {P : Polynomial ℚ} (I J : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P)
    (D : ℕ) (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    {S : Scheme.{u}} {ι : Type v}
    (x : ι → (S ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I.ideal)))
    (y : ι → (S ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J.ideal)))
    (hx : Section.DetectionByFamilies.SectionsDetectedBy (ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal D) x)
    (hy : Section.DetectionByFamilies.SectionsDetectedBy (ProjectiveTwisting.Bundle.projectiveTwistingBundle J.ideal D) y)
    (hxy : ∀ c, x c ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal = y c ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J.ideal) :
    I = J := by
  apply SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.ext
  exact HilbertScheme.Presentations.Uniform.FamilyReconstruction.GradedHilbert.uniformFamily_eq_of_degreeRelations_eq I.ideal I.saturated P I.hilbert
    J.ideal J.saturated J.hilbert D hD
    (degreeRelations_eq_of_detectingFamilies I.ideal J.ideal I.saturated J.saturated x y hx hy hxy)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.ConfigurationDeterminesIdeal
