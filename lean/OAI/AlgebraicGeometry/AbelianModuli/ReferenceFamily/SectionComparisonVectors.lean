import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveLocalVectors
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionComparisonGauges
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension

/-! # Section Comparison Vectors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionComparisonVectors

noncomputable section

section

/-! The enlarged local vectors for two actual section morphisms are
holomorphic, nowhere zero, and proportional on their native overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf))
    (t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf))
    (hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j))
    (g : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := SectionComparisonGauges.sectionComparisonOpen V s t i))ˣ)

def sectionComparisonVector (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace) :
    Fin ((n + m + 1) + 1) → ℂ :=
  ProjectiveLocalVectors.projectiveComparisonVector (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x)
    (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (g i).val x)

theorem sectionComparisonVector_holomorphic (i : Fin (n + 1) × Fin (m + 1)) :
    ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin ((n + m + 1) + 1) → ℂ) ∞
      (sectionComparisonVector V s t hs ht g i) (SectionComparisonGauges.sectionComparisonOpen V s t i) := by
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
    change ContMDiffOn _ _ ∞ (fun x => ProjectiveLocalVectors.projectiveComparisonVector
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x)
        i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (g i).val x) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl k))) _
    simp only [ProjectiveLocalVectors.projectiveComparisonVector_left]
    exact contMDiffOn_pi_space.mp hL k
  | inr k =>
    change ContMDiffOn _ _ ∞ (fun x => ProjectiveLocalVectors.projectiveComparisonVector
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x)
        i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (g i).val x) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr k))) _
    simp only [ProjectiveLocalVectors.projectiveComparisonVector_right]
    apply (contMDiffOn_pi_space.mp hK k).div₀ (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_contMDiffOn (g i).val)
    intro x hx
    rw [DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_apply (g i).val x hx]
    exact DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (g i) ⟨x, hx⟩

theorem sectionComparisonVector_ne_zero (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) : sectionComparisonVector V s t hs ht g i x ≠ 0 :=
  ProjectiveLocalVectors.projectiveComparisonVector_ne_zero _ _ i _
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i.1 x).mpr hi.1)

theorem sectionComparisonVector_compatible
    (hg : ∀ i j (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i)
      (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j),
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) /
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) =
          (g j).val ⟨x, hj⟩ / (g i).val ⟨x, hi⟩)
    (i j : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j) :
    ∃ c : ℂ, c • sectionComparisonVector V s t hs ht g j x = sectionComparisonVector V s t hs ht g i x := by
  refine ⟨Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x), ?_⟩
  unfold sectionComparisonVector
  rw [DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_apply (g i).val x hi, DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_apply (g j).val x hj]
  exact ProjectiveLocalVectors.projectiveComparisonVector_change _ _ i j _ _
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i.1 x).mpr hi.1)
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs j.1 x).mpr hj.1)
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht i.2 x).mpr hi.2)
    ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht j.2 x).mpr hj.2)
    (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (g i) ⟨x, hi⟩) (hg i j x hi hj)

end

/-! Algebraize the actual enlarged projective map of two generating
section families with equal native holomorphic line classes. Every
original coordinate and every comparison gauge is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf))
    (t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf))
    (hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j))

structure SectionComparisonAlgebraization where
  gauge : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := SectionComparisonGauges.sectionComparisonOpen V s t i))ˣ
  gauge_law : ∀ i j (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i)
      (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j),
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) /
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) =
        (gauge j).val ⟨x, hj⟩ / (gauge i).val ⟨x, hi⟩
  map : V.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + m + 1))
  map_value : ∀ i (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i),
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map map x = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (n + m + 1)
      (Projectivization.mk ℂ (sectionComparisonVector V s t hs ht gauge i x)
        (sectionComparisonVector_ne_zero V s t hs ht gauge i x hi))

theorem sectionComparisonAlgebraization_nonempty
    (he : Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass V L = Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass V K) :
    Nonempty (SectionComparisonAlgebraization V s t hs ht) := by
  obtain ⟨g, hg⟩ := SectionComparisonGauges.exists_sectionComparisonGauges V s t hs ht he
  let U := SectionComparisonGauges.sectionComparisonOpen V s t
  let hU := SectionComparisonGauges.sectionComparisonOpen_covers V s t hs ht
  let v := sectionComparisonVector V s t hs ht g
  let hv := fun i => (sectionComparisonVector_holomorphic V s t hs ht g i).continuousOn
  let hn := sectionComparisonVector_ne_zero V s t hs ht g
  let hc := sectionComparisonVector_compatible V s t hs ht g hg
  let p := ProjectiveLocalVectors.gluedProjectiveVectorMap U hU v hv hn hc
  obtain ⟨f, hf⟩ := ProjectiveMapAlgebraization.exists_algebraic_projectiveMap V p p.continuous
    (ProjectiveLocalVectors.gluedProjectiveVectorMap_holomorphic U hU v hv hn hc
      (sectionComparisonVector_holomorphic V s t hs ht g))
  refine ⟨⟨g, hg, f, ?_⟩⟩
  intro i x hi
  exact (hf x).trans (congrArg (ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (n + m + 1))
    (ProjectiveLocalVectors.gluedProjectiveVectorMap_apply U hU v hv hn hc i x hi))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionComparisonVectors
