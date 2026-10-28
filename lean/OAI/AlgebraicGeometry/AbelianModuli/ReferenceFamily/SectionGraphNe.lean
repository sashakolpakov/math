import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveLocalVectors
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionComparisonGauges
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension

/-! # Section Graph Ne -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionGraphNe

noncomputable section

/-! Compatible holomorphic coefficients of a morphism between two
generated line bundles determine an actual algebraic projective graph
map. The construction allows its coefficient to vanish. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf))
    (t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf))
    (hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j))
    (c : ∀ i, DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := SectionComparisonGauges.sectionComparisonOpen V s t i))

def sectionGraphVector (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace) :
    Fin ((n + m + 1) + 1) → ℂ :=
  ProjectiveLocalVectors.projectiveSectionVector (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x)
    (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (c i) x)

theorem sectionGraphVector_holomorphic (i : Fin (n + 1) × Fin (m + 1)) :
    ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin ((n + m + 1) + 1) → ℂ) ∞
      (sectionGraphVector V s t hs ht c i) (SectionComparisonGauges.sectionComparisonOpen V s t i) := by
  have hL := (SectionChernComparison.nativeSectionCoordinates_holomorphic V s hs i.1).mono
    (fun x (hx : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) =>
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i.1 x).mpr hx.1)
  have hK := (SectionChernComparison.nativeSectionCoordinates_holomorphic V t ht i.2).mono
    (fun x (hx : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) =>
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht i.2 x).mpr hx.2)
  apply contMDiffOn_pi_space.mpr
  intro k
  obtain ⟨k, rfl⟩ := (ProjectiveLocalVectors.comparisonCoordinateEquiv n m).surjective k
  cases k with
  | inl k =>
    change ContMDiffOn _ _ ∞ (fun x => ProjectiveLocalVectors.projectiveSectionVector
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x)
        i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (c i) x) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl k))) _
    simp only [ProjectiveLocalVectors.projectiveSectionVector_left]
    exact contMDiffOn_pi_space.mp hL k
  | inr k =>
    change ContMDiffOn _ _ ∞ (fun x => ProjectiveLocalVectors.projectiveSectionVector
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x)
        i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (c i) x) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr k))) _
    simp only [ProjectiveLocalVectors.projectiveSectionVector_right]
    exact (contMDiffOn_pi_space.mp hK k).mul (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_contMDiffOn (c i))

theorem sectionGraphVector_ne_zero (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) : sectionGraphVector V s t hs ht c i x ≠ 0 :=
  ProjectiveLocalVectors.projectiveSectionVector_ne_zero _ _ i _
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i.1 x).mpr hi.1)

theorem sectionGraphVector_compatible
    (hc : ∀ i j (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i)
      (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j),
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) * c j ⟨x, hj⟩ =
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) * c i ⟨x, hi⟩)
    (i j : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j) :
    ∃ a : ℂ, a • sectionGraphVector V s t hs ht c j x = sectionGraphVector V s t hs ht c i x := by
  refine ⟨Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x), ?_⟩
  unfold sectionGraphVector
  rw [DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_apply (c i) x hi, DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_apply (c j) x hj]
  exact ProjectiveLocalVectors.projectiveSectionVector_change _ _ i j _ _
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i.1 x).mpr hi.1)
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs j.1 x).mpr hj.1)
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht i.2 x).mpr hi.2)
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht j.2 x).mpr hj.2) (hc i j x hi hj)

theorem exists_sectionGraphAlgebraization
    (hc : ∀ i j (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i)
      (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j),
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) * c j ⟨x, hj⟩ =
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) * c i ⟨x, hi⟩) :
    ∃ f : V.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + m + 1)),
      ∀ i (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i),
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (n + m + 1)
          (Projectivization.mk ℂ (sectionGraphVector V s t hs ht c i x)
            (sectionGraphVector_ne_zero V s t hs ht c i x hi)) := by
  let U := SectionComparisonGauges.sectionComparisonOpen V s t
  let hU := SectionComparisonGauges.sectionComparisonOpen_covers V s t hs ht
  let v := sectionGraphVector V s t hs ht c
  let hv := fun i => (sectionGraphVector_holomorphic V s t hs ht c i).continuousOn
  let hn := sectionGraphVector_ne_zero V s t hs ht c
  let hvv := sectionGraphVector_compatible V s t hs ht c hc
  let p := ProjectiveLocalVectors.gluedProjectiveVectorMap U hU v hv hn hvv
  obtain ⟨f, hf⟩ := ProjectiveMapAlgebraization.exists_algebraic_projectiveMap V p p.continuous
    (ProjectiveLocalVectors.gluedProjectiveVectorMap_holomorphic U hU v hv hn hvv
      (sectionGraphVector_holomorphic V s t hs ht c))
  refine ⟨f, ?_⟩
  intro i x hi
  exact (hf x).trans (congrArg (ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (n + m + 1))
    (ProjectiveLocalVectors.gluedProjectiveVectorMap_apply U hU v hv hn hvv i x hi))

structure SectionGraphAlgebraization where
  map : V.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + m + 1))
  map_value : ∀ i (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i),
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map map x = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (n + m + 1)
      (Projectivization.mk ℂ (sectionGraphVector V s t hs ht c i x)
        (sectionGraphVector_ne_zero V s t hs ht c i x hi))

theorem sectionGraphAlgebraization_nonempty
    (hc : ∀ i j (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i)
      (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j),
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) * c j ⟨x, hj⟩ =
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) * c i ⟨x, hi⟩) :
    Nonempty (SectionGraphAlgebraization V s t hs ht c) := by
  obtain ⟨f, hf⟩ := exists_sectionGraphAlgebraization V s t hs ht c hc
  exact ⟨⟨f, hf⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionGraphNe
