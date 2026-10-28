import OAI.AlgebraicGeometry.Resolution.Blowups.ReesProjectiveComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedProjectiveSectionOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapGluing

/-! # Projective Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ProjectiveMap.Construction

noncomputable section

/-! A global complex projective coordinate map on the actual glued Rees blowup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X : Scheme} {n : ℕ}
variable (e : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) [IsClosedImmersion e] (I : X.IdealSheafData)

/-- Actual common-degree equations for a center on the projective scheme. -/
structure ProjectiveCenterEquations where
  dimension : ℕ
  degree : ℕ
  forms : Fin (dimension + 1) → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n
  positive : 0 < degree
  homogeneous : ∀ j, (forms j).IsHomogeneous degree
  generates : ∀ i : Fin (n + 1),
    Ideal.span (Set.range (fun j => ClosedProjectiveIdealGenerators.Construction.closedProjectiveDehomogenize e i (forms j))) =
      I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i)

/-- The equations exist for every ideal sheaf, by homogeneous ideal recovery. -/
def projectiveCenterEquations : ProjectiveCenterEquations e I := Classical.choice (by
  obtain ⟨m, D, p, hD, hhom, hgen⟩ :=
    ClosedProjectiveIdealGenerators.Construction.closedProjective_idealSheaf_exists_common_degree_generators e I
  exact ⟨⟨m, D, p, hD, hhom, hgen⟩⟩)

variable {e I} (Q : ProjectiveCenterEquations e I)

def projectiveCenterChartGenerator (i : Fin (n + 1)) (j : Fin (Q.dimension + 1)) :
    I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i) :=
  ⟨ClosedProjectiveIdealGenerators.Construction.closedProjectiveDehomogenize e i (Q.forms j), by
    rw [← Q.generates i]
    exact Ideal.subset_span ⟨j, rfl⟩⟩

theorem projectiveCenterChartGenerator_span (i : Fin (n + 1)) :
    Submodule.span Γ(X, ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i)
      (Set.range (projectiveCenterChartGenerator Q i)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i))
    (fun j => (projectiveCenterChartGenerator Q i j).property)).mpr
  exact Q.generates i

def projectiveCenterChartMap (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (i : Fin (n + 1)) :
    ReesGrading.Construction.affineBlowup (I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i)) ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace Q.dimension :=
  ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap _ (Affine.ComplexNaturality.Construction.affineComplexScalars f (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i))
    (projectiveCenterChartGenerator Q i) (projectiveCenterChartGenerator_span Q i)

variable [IsIntegral X] [IsLocallyNoetherian X] (hI : I ≠ ⊥)

theorem projectiveCenterChartMap_over (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (i : Fin (n + 1)) :
    projectiveCenterChartMap Q f i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension =
      Data.Construction.globalBlowupChart I hI (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i) ≫ Data.Construction.globalBlowupToBase I hI ≫ f := by
  rw [projectiveCenterChartMap, ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap_over, Affine.ComplexNaturality.Construction.affineComplexScalars_spec,
    ← Category.assoc, ← Data.Construction.globalBlowupChart_over, Category.assoc]

include hI in
/-- The actual projective maps agree after restriction to every common affine open. -/
theorem projectiveCenterChartMap_affine_overlap
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (i j : Fin (n + 1)) (W : X.affineOpens)
    (hWi : W ≤ ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i) (hWj : W ≤ ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e j) :
    (Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hWi) ≫ projectiveCenterChartMap Q f i =
      (Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hWj) ≫ projectiveCenterChartMap Q f j := by
  let : IsReduced (ReesGrading.Construction.affineBlowup (I.ideal W)) :=
    isReduced_of_isOpenImmersion (Data.Construction.globalBlowupChart I hI W)
  let : LocallyOfFiniteType
      (ReesGrading.Construction.affineBlowupToSpec (I.ideal W) ≫ Spec.map (CommRingCat.ofHom (Affine.ComplexNaturality.Construction.affineComplexScalars f W))) := by
    rw [Affine.ComplexNaturality.Construction.affineComplexScalars_spec, ← Category.assoc, ← Data.Construction.globalBlowupChart_over I hI W,
      Category.assoc]
    infer_instance
  obtain ⟨u, hu, hp⟩ := ClosedProjectiveSectionOverlap.Construction.closedProjective_forms_common_unit e j i hWj hWi Q.degree
  apply ReesProjectiveComparison.Construction.reesProjectiveCoordinateMap_common_unit
    (I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i)) (I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e j))
    (I.ideal W) (Affine.ComplexNaturality.Construction.affineComplexScalars f _) (Affine.ComplexNaturality.Construction.affineComplexScalars f _) (Affine.ComplexNaturality.Construction.affineComplexScalars f W)
    (Blowup.Functor.Construction.affineRestriction hWi) (Blowup.Functor.Construction.affineRestriction hWj)
    (Affine.ComplexNaturality.Construction.affineComplexScalars_restrict f hWi) (Affine.ComplexNaturality.Construction.affineComplexScalars_restrict f hWj)
    (Blowup.Functor.Construction.affineRestriction_ideal I hWi) (Blowup.Functor.Construction.affineRestriction_ideal I hWj)
    (projectiveCenterChartGenerator Q i) (projectiveCenterChartGenerator Q j)
    (projectiveCenterChartGenerator_span Q i) (projectiveCenterChartGenerator_span Q j) u hu
  intro k
  exact hp (Q.forms k) (Q.homogeneous k)

omit [IsIntegral X] [IsLocallyNoetherian X] in
theorem closedProjectiveAffineOpen_iSup :
    (⨆ i, (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i).1) = ⊤ := by
  change (⨆ i, e ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading ℂ n) (MvPolynomial.X i)) = ⊤
  rw [← Scheme.Hom.preimage_iSup,
    Proj.iSup_basicOpen_eq_top _ _ PolynomialProjectiveBaseChange.Construction.polynomial_irrelevant_le_span_variables,
    Scheme.Hom.preimage_top]

/-- The local projective coordinates glue on the already constructed global blowup. -/
def globalBlowupProjectiveMap (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    Data.Construction.globalBlowup I hI ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace Q.dimension :=
  (MapGluing.Construction.globalBlowupChosenCover I hI (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e) closedProjectiveAffineOpen_iSup).glueMorphisms
    (projectiveCenterChartMap Q f) (fun i j =>
      MapGluing.Construction.globalBlowupChart_overlap_map_eq I hI f (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension)
        (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i) (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e j)
        (projectiveCenterChartMap Q f i) (projectiveCenterChartMap Q f j)
        (projectiveCenterChartMap_over Q hI f i) (projectiveCenterChartMap_over Q hI f j)
        (projectiveCenterChartMap_affine_overlap Q hI f i j))

theorem globalBlowupProjectiveMap_chart (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (i : Fin (n + 1)) :
    Data.Construction.globalBlowupChart I hI (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i) ≫ globalBlowupProjectiveMap Q hI f =
      projectiveCenterChartMap Q f i :=
  (MapGluing.Construction.globalBlowupChosenCover I hI (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e)
    closedProjectiveAffineOpen_iSup).ι_glueMorphisms _ _ i

theorem globalBlowupProjectiveMap_over (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    globalBlowupProjectiveMap Q hI f ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension =
      Data.Construction.globalBlowupToBase I hI ≫ f := by
  apply (MapGluing.Construction.globalBlowupChosenCover I hI (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e)
    closedProjectiveAffineOpen_iSup).hom_ext
  intro i
  change Fin (n + 1) at i
  change Data.Construction.globalBlowupChart I hI (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i) ≫
    (globalBlowupProjectiveMap Q hI f ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension) =
      Data.Construction.globalBlowupChart I hI (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i) ≫ Data.Construction.globalBlowupToBase I hI ≫ f
  rw [← Category.assoc, globalBlowupProjectiveMap_chart, projectiveCenterChartMap_over Q hI]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ProjectiveMap.Construction
