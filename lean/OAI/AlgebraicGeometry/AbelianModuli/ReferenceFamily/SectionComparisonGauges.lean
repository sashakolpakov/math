import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicComparisonGauges
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionChernComparison

/-! # Section Comparison Gauges -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionComparisonGauges

noncomputable section

/-! Equal native holomorphic classes give comparison gauges on the
actual common nonvanishing cover of two generating section families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf))
    (t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf))

def sectionComparisonOpen (i : Fin (n + 1) × Fin (m + 1)) : Opens V.analyticSpace :=
  AnalyticFrameTransitions.frameAnalyticOpen V.presentation (SectionLocalFrames.sectionLocalFrame (s i.1)) ⊓
    AnalyticFrameTransitions.frameAnalyticOpen V.presentation (SectionLocalFrames.sectionLocalFrame (t i.2))

theorem sectionComparisonOpen_covers
    (hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j)) (x : V.analyticSpace) :
    ∃ i, x ∈ sectionComparisonOpen V s t i := by
  obtain ⟨i, hi⟩ := hs (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)
  obtain ⟨j, hj⟩ := ht (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)
  exact ⟨(i, j), hi, hj⟩

theorem exists_sectionComparisonGauges
    (hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j))
    (he : Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass V L = Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass V K) :
    ∃ g : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := sectionComparisonOpen V s t i))ˣ,
      ∀ i j (x : V.analyticSpace) (hi : x ∈ sectionComparisonOpen V s t i)
        (hj : x ∈ sectionComparisonOpen V s t j),
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) /
          Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) =
            (g j).val ⟨x, hj⟩ / (g i).val ⟨x, hi⟩ := by
  let U := sectionComparisonOpen V s t
  obtain ⟨g, hg⟩ := Intrinsic.HolomorphicComparisonGauges.exists_nativeHolomorphicComparisonGauges V L K he U
    (sectionComparisonOpen_covers V s t hs ht)
    (fun i => SectionLocalFrames.sectionLocalFrame (s i.1)) (fun i => SectionLocalFrames.sectionLocalFrame (t i.2))
    (fun _ => inf_le_left) (fun _ => inf_le_right)
  refine ⟨g, ?_⟩
  intro i j x hi hj
  let b : Fin 2 → Fin (n + 1) × Fin (m + 1) := ![i, j]
  have hx : x ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U b := by
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U b x).mpr
    intro k
    fin_cases k
    · exact hi
    · exact hj
  have h := hg b ⟨x, hx⟩
  have hL := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_ratio V.presentation s hs i.1 j.1 x hi.1).trans
    (SectionFrameEvaluation.sectionFrame_pointTransition V.presentation (s i.1) (s j.1) x hi.1 hj.1).symm
  have hK := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_ratio V.presentation t ht i.2 j.2 x hi.2).trans
    (SectionFrameEvaluation.sectionFrame_pointTransition V.presentation (t i.2) (t j.2) x hi.2 hj.2).symm
  exact (congrArg₂ (· / ·) hL hK).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionComparisonGauges
