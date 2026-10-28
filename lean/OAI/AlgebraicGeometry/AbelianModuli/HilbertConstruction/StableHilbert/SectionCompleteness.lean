import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CoordinateCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion

/-! # Section Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SectionCompleteness.StableHilbertCoverage

noncomputable section

/-! Bijectivity of the homogeneous degree-one map gives completeness of
the original coordinate section family over the actual global base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped BigOperators
universe u v

def linearCoordinateVector (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n 1 := ⟨X i, isHomogeneous_X R i⟩

def linearCoordinateBasis (R : Type u) [CommRing R] (n : ℕ) :
    Module.Basis (Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n 1) := by
  have hi : LinearIndependent R (linearCoordinateVector R n) := by
    apply LinearIndependent.of_comp (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n 1).subtype
    exact MvPolynomial.linearIndependent_X (Fin (n + 1)) R
  have hs : ⊤ ≤ Submodule.span R (Set.range (linearCoordinateVector R n)) := by
    intro p _
    have hp : p.val ∈ Submodule.span R (Set.range (X : Fin (n + 1) → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) := by
      rw [← homogeneousSubmodule_one_eq_span_X]
      exact p.property
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hp
    have he : ∑ i, c i • linearCoordinateVector R n i = p := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul, linearCoordinateVector] using hc
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Module.Basis.mk hi hs

theorem linearCoordinateBasis_apply (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    linearCoordinateBasis R n i = linearCoordinateVector R n i := by
  unfold linearCoordinateBasis
  exact congrFun (Module.Basis.coe_mk _ _) i

def spectrumCoefficientBasis {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (M : X.Modules) {ι : Type v}
    (b : Module.Basis ι R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M)) :
    Module.Basis ι Γ(Spec (.of R), ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M) := by
  letI : Module Γ(Spec (.of R), ⊤) ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) :=
    inferInstanceAs (Module Γ(Spec (.of R), ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M))
  exact b.mapCoeffs (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv (fun _ _ => rfl)

theorem spectrumCoefficientBasis_apply {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (M : X.Modules) {ι : Type v}
    (b : Module.Basis ι R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M)) (i : ι) :
    (spectrumCoefficientBasis p M b i : (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) = b i := by
  let : Module Γ(Spec (.of R), ⊤) ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) :=
    inferInstanceAs (Module Γ(Spec (.of R), ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M))
  exact b.mapCoeffs_apply (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
    (fun _ _ => rfl) i

theorem spectrumCoefficientBasis_family {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (M : X.Modules) {ι : Type v}
    (b : Module.Basis ι R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M)) :
    Coefficient.RingSectionBasis.coefficientRingBasisFamily p.appTop.hom M (spectrumCoefficientBasis p M b) =
      Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap p) M b := by
  funext i
  exact congrArg ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) M).symm)
    (spectrumCoefficientBasis_apply p M b i)

theorem coordinateSections_bijective_of_polynomialMap {R : Type u} [CommRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (hI : Function.Bijective (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I 1)) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).appTop.hom
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I)) := by
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
  let M := (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf
  let e := LinearEquiv.ofBijective (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I 1) hI
  let b := (linearCoordinateBasis R n).map e
  apply (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff p.appTop.hom M
    (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I)).mpr
  refine ⟨spectrumCoefficientBasis p M b, ?_⟩
  rw [spectrumCoefficientBasis_family]
  funext i
  have hb : b i = SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I 1 (linearCoordinateVector R n i) := by
    change e (linearCoordinateBasis R n i) = _
    rw [linearCoordinateBasis_apply]
    rfl
  change (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) M).symm (b i) = _
  rw [hb]
  exact CoordinateCompleteness.StableHilbertCoverage.polynomialLinearSection_eq_coordinate I i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SectionCompleteness.StableHilbertCoverage
