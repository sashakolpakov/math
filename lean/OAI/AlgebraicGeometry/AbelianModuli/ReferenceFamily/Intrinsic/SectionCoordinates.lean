import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SectionMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveChartPoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SectionCoordinates

noncomputable section

section

/-! The native projective point of a section morphism has the actual
evaluated section ratios as its normalized homogeneous coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages

def nativeSectionCoordinates (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {M : X.left.Modules} {n : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule X.left ⟶ M))
    (hs : ∀ x : X.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → Projectivization ℂ (Fin (n + 1) → ℂ) :=
  fun p => (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SectionMorphism.nativeSectionMorphism X s hs) p)

theorem nativeSectionCoordinates_continuous (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {M : X.left.Modules} {n : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule X.left ⟶ M))
    (hs : ∀ x : X.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) :
    Continuous (nativeSectionCoordinates X s hs) :=
  (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.continuous.comp
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (SectionMorphism.nativeSectionMorphism X s hs)).continuous

theorem projectiveAffineSchemePoint_ratios {n : ℕ} (v : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) (hi : v i = 1) (j : Fin (n + 1)) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm
      (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i (fun k => v k.val))) = v j := by
  let z (k : {k : Fin (n + 1) // k ≠ i}) := v k.val
  let q := (ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).symm z
  have he : (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i z) = q.val :=
    (congrArg (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm
      (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint_eq_projectivization n i z)).trans
        ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm_apply_apply q.val)
  rw [he]
  by_cases hji : j = i
  · subst j
    exact q.property.trans hi.symm
  · exact congrFun ((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).apply_symm_apply z) ⟨j, hji⟩

theorem nativeSectionCoordinates_ratio (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    {M : P.carrier.Modules} {n : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule P.carrier ⟶ M))
    (hs : ∀ x : P.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (i j : Fin (n + 1)) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hp : p ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j (nativeSectionCoordinates P.toOver s hs p) =
      DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))).symm ⟨p, hp⟩)
        (HilbertConstruction.Section.Frames.sectionRatio (s i) (s j)) := by
  let D := HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)
  let q := (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P D).symm ⟨p, hp⟩
  let v (j : Fin (n + 1)) := DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation q (HilbertConstruction.Section.Frames.sectionRatio (s i) (s j))
  have hv : v i = 1 := by
    change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation q (HilbertConstruction.Section.Frames.sectionRatio (s i) (s i)) = 1
    rw [HilbertConstruction.Section.Frames.sectionRatio_self, map_one]
  have hq : q.left ≫ D.ι = p.left := congrArg (fun r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver => r.left)
    (congrArg Subtype.val ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P D).apply_symm_apply ⟨p, hp⟩))
  have hpoint : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SectionMorphism.nativeSectionMorphism P.toOver s hs) p =
      ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i (fun j => v j.val) := by
    apply Over.OverMorphism.ext
    change p.left ≫ (SectionMorphism.nativeSectionMorphism P.toOver s hs).left = _
    exact (congrArg (fun z => z ≫ (SectionMorphism.nativeSectionMorphism P.toOver s hs).left) hq.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => q.left ≫ z) (SectionMorphism.nativeSectionMorphism_restrict P.toOver s hs i)).trans
          ((ProjectiveChartPoints.projectiveChartMap_point q (fun j => HilbertConstruction.Section.Frames.sectionRatio (s i) (s j)) i (HilbertConstruction.Section.Frames.sectionRatio_self (s i))).trans
            (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint_left n i (fun j => v j.val)).symm)))
  exact (congrArg (fun z => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm z)) hpoint).trans
    (projectiveAffineSchemePoint_ratios v i hv j)

end

/-! The analytic homogeneous-coordinate patches of the actual section
morphism are exactly the original section nonvanishing opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages

theorem nativeSectionMorphism_preimage (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {M : X.left.Modules} {n : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule X.left ⟶ M))
    (hs : ∀ x : X.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) (i : Fin (n + 1)) :
    (SectionMorphism.nativeSectionMorphism X s hs).left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i = HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  have h : ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i =
      Proj.basicOpen (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) n) (MvPolynomial.X i) :=
    (Proj.map_preimage_basicOpen (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n)
      (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap_irrelevant ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n) (MvPolynomial.X i)).trans
      (congrArg (Proj.basicOpen (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) n))
        (ProjectiveChartCoefficients.ProjectiveCoefficients.gradedMap_X ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n i))
  exact (congrArg (fun f => f ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (SectionMorphism.nativeSectionMorphism_left X s hs)).trans
      ((congrArg (fun U => HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism X.hom s hs ⁻¹ᵁ U) h).trans
        (HilbertConstruction.ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage X.hom s hs i))

theorem nativeSectionCoordinates_inPatch (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    {M : P.carrier.Modules} {n : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule P.carrier ⟶ M))
    (hs : ∀ x : P.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (i : Fin (n + 1)) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (nativeSectionCoordinates P.toOver s hs p) ↔
      p ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) := by
  have hp := ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen n i (nativeSectionCoordinates P.toOver s hs p)
  have hq : ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (nativeSectionCoordinates P.toOver s hs p) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SectionMorphism.nativeSectionMorphism P.toOver s hs) p :=
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).apply_symm_apply _
  rw [hq] at hp
  have he := congrArg (fun U : P.carrier.Opens => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ U)
    (nativeSectionMorphism_preimage P.toOver s hs i)
  exact hp.symm.trans he.to_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SectionCoordinates
