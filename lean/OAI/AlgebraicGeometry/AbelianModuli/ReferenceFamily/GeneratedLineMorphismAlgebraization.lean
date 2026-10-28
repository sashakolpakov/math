import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GeneratedHolomorphicMorphismValues
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LineMorphismCoefficients

/-! # Generated Line Morphism Algebraization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Every compatible native holomorphic coefficient family between
two generated algebraic line bundles comes from an actual algebraic
morphism, with agreement in every actual local frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier}
    (D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V K L) {n m : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf))
    (t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf))

def Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.sectionCoefficient (i : Fin (n + 1) × Fin (m + 1)) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := SectionComparisonGauges.sectionComparisonOpen V s t i) :=
  DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction
    (show SectionComparisonGauges.sectionComparisonOpen V s t i ≤
      AnalyticFrameTransitions.frameAnalyticOpen V.presentation (SectionLocalFrames.sectionLocalFrame (t i.2)) ⊓
        AnalyticFrameTransitions.frameAnalyticOpen V.presentation (SectionLocalFrames.sectionLocalFrame (s i.1)) from fun _ hx => ⟨hx.2, hx.1⟩)
    (D.coefficient (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1)))

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.sectionCoefficient_value (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) :
    D.sectionCoefficient s t i ⟨x, hi⟩ =
      D.coefficient (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1)) ⟨x, hi.2, hi.1⟩ := rfl

variable (hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j))

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.sectionCoefficient_compatible (i j : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) * D.sectionCoefficient s t j ⟨x, hj⟩ =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) * D.sectionCoefficient s t i ⟨x, hi⟩ := by
  have hL := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_ratio V.presentation s hs i.1 j.1 x hi.1).trans
    (SectionFrameEvaluation.sectionFrame_pointTransition V.presentation (s i.1) (s j.1) x hi.1 hj.1).symm
  have hK := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_ratio V.presentation t ht i.2 j.2 x hi.2).trans
    (SectionFrameEvaluation.sectionFrame_pointTransition V.presentation (t i.2) (t j.2) x hi.2 hj.2).symm
  rw [hL, hK, D.sectionCoefficient_value s t i x hi, D.sectionCoefficient_value s t j x hj]
  exact (mul_comm _ _).trans (D.frame_change (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (t j.2))
    (SectionLocalFrames.sectionLocalFrame (s i.1)) (SectionLocalFrames.sectionLocalFrame (s j.1)) x ⟨hi.2, hi.1⟩ ⟨hj.2, hj.1⟩).symm

include hs ht in
theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.exists_algebraic_of_generated :
    ∃ f : K.sheaf ⟶ L.sheaf, Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V K L f = D := by
  obtain ⟨A, ⟨B⟩⟩ := GeneratedHolomorphicMorphisms.generated_holomorphicMorphism_algebraization V s t hs ht (D.sectionCoefficient s t)
    (D.sectionCoefficient_compatible s t hs ht)
  refine ⟨B.map, ?_⟩
  apply Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.ext V
  intro r q
  apply ContMDiffMap.ext
  intro x
  change LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient V B.map r q x = D.coefficient r q x
  obtain ⟨i, hi⟩ := SectionComparisonGauges.sectionComparisonOpen_covers V s t hs ht x.val
  have hlocal : LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient V B.map
      (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1)) ⟨x.val, hi.2, hi.1⟩ =
    D.coefficient (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1)) ⟨x.val, hi.2, hi.1⟩ :=
    (LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient_value_on_open V B.map
      (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1)) (A.regularOpen i)
        inf_le_right inf_le_left x.val hi).trans
      ((B.coefficient_value i x.val hi).trans (D.sectionCoefficient_value s t i x.val hi))
  have hB := LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient_frame_change V B.map r (SectionLocalFrames.sectionLocalFrame (t i.2))
    q (SectionLocalFrames.sectionLocalFrame (s i.1)) x.val x.property ⟨hi.2, hi.1⟩
  have hD := D.frame_change r (SectionLocalFrames.sectionLocalFrame (t i.2)) q (SectionLocalFrames.sectionLocalFrame (s i.1))
    x.val x.property ⟨hi.2, hi.1⟩
  apply mul_left_cancel₀ (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation r (SectionLocalFrames.sectionLocalFrame (t i.2))
    ⟨x.val, x.property.1, hi.2⟩)
  exact hB.trans ((congrArg (fun a => a * AnalyticFrameTransitions.framePointTransition V.presentation q (SectionLocalFrames.sectionLocalFrame (s i.1))
    x.val x.property.2 hi.1) hlocal).trans hD.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
