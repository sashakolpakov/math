import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.RestrictionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Cover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionAgreement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PairCompatibility

/-! # Cech Chart Agreement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechChartAgreement

noncomputable section

/-! Compatibility of actual projective chart functions is exactly the first coordinate Čech kernel condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateChartPairAgreement_iff (i j : Fin (n + 1))
    (x : Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}))
    (y : Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j})) :
    Cech.PairDifferential.moduleCechPairRestrictionLeft R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) i j
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I {i} (Finset.singleton_nonempty i) x).val =
      Cech.PairDifferential.moduleCechPairRestrictionRight R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) i j
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I {j} (Finset.singleton_nonempty j) y).val ↔
    (AlgebraSectionModules.algebraSectionModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))).map
      (homOfLE (show ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j} ≤
        ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} from inf_le_left)).op x =
    (AlgebraSectionModules.algebraSectionModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))).map
      (homOfLE (show ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j} ≤
        ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j} from inf_le_right)).op y := by
  let hL : ({i} : Finset (Fin (n + 1))) ⊆ {i, j} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j})
  let hR : ({j} : Finset (Fin (n + 1))) ⊆ {i, j} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  let hp : ({i, j} : Finset (Fin (n + 1))).Nonempty := ⟨i, Finset.mem_insert_self i {j}⟩
  have hl := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartSectionEquiv_restriction I (Finset.singleton_nonempty i) hp hL x
  have hr := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartSectionEquiv_restriction I (Finset.singleton_nonempty j) hp hR y
  have hi : Function.Injective (fun z : Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i, j}) => (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I {i, j} hp z).val) :=
    Subtype.val_injective.comp (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I {i, j} hp).injective
  exact (congrArg₂ Eq hl.symm hr.symm).to_iff.trans (hi.eq_iff.trans
    (Open.SectionAgreement.openSectionPair_iff_of_open_eq
      (AlgebraSectionModules.algebraSectionModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))))
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I hL) (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I hR)
      (ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_pair I i j) x y))

theorem coordinateChartTupleCechEquiv_singleton
    (x : (i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}))
    (i : Fin (n + 1)) :
    (ProjectiveCoordinate.Cover.coordinateChartTupleCechEquiv I x).val {i} =
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I {i} (Finset.singleton_nonempty i) (x i)).val := by
  let e := Cech.SingletonCoordinates.moduleCechOneTermEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0
  let y := fun j => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I {j} (Finset.singleton_nonempty j) (x j)
  exact (Cech.SingletonCoordinates.moduleCechOneTermEquiv_apply R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 (e.symm y) i).symm.trans
    (congrArg (fun z => (z i).val) (e.apply_symm_apply y))

theorem coordinateChartTupleCechEquiv_kernel_iff
    (x : (i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) :
    ProjectiveCoordinate.Cover.coordinateChartTupleCechEquiv I x ∈
      (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 1).ker ↔
    x ∈ Module.SheafOverlapEquivalence.compatibleOpenSectionModule
      (AlgebraSectionModules.algebraSectionModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))))
      (fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) := by
  refine (Cech.PairCompatibility.moduleCech_one_cocycle_iff R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 (ProjectiveCoordinate.Cover.coordinateChartTupleCechEquiv I x)).trans
    (Iff.trans ?_ (Open.SectionAgreement.compatibleOpenSectionModule_iff_ordered
      (AlgebraSectionModules.algebraSectionModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))))
      (fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) x).symm)
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro _
  exact (congrArg₂ Eq
    (congrArg (Cech.PairDifferential.moduleCechPairRestrictionLeft R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) i j)
      (coordinateChartTupleCechEquiv_singleton I x i))
    (congrArg (Cech.PairDifferential.moduleCechPairRestrictionRight R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) i j)
      (coordinateChartTupleCechEquiv_singleton I x j))).to_iff.trans (coordinateChartPairAgreement_iff I i j (x i) (x j))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechChartAgreement
