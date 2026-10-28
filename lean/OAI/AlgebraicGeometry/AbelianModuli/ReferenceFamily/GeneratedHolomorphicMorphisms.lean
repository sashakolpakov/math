import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionGraphRegularCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularMapGluing

/-! # Generated Holomorphic Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Compatible holomorphic coefficients between two generated line
bundles are the native coordinates of an actual algebraic sheaf morphism.
The regular coefficients and the local formulas are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf))
    (t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf))
    (hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j))
    (c : ∀ i, DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := SectionComparisonGauges.sectionComparisonOpen V s t i))
    (hc : ∀ i j (x : V.analyticSpace) (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i)
      (hj : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t j),
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) * c j ⟨x, hj⟩ =
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) * c i ⟨x, hi⟩)

section

structure SectionGraphNe.SectionGraphAlgebraization.AlgebraicMorphism (A : SectionGraphNe.SectionGraphAlgebraization V s t hs ht c) where
  map : K.sheaf ⟶ L.sheaf
  map_local : ∀ i,
    map.over (A.regularOpen i) = Intrinsic.RegularMapGluing.nativeFramedRegularMap V K L (A.regularOpen i)
      (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1)) inf_le_right inf_le_left
      (A.regularCoefficient i)

include hc in
theorem SectionGraphNe.SectionGraphAlgebraization.exists_algebraicMorphism (A : SectionGraphNe.SectionGraphAlgebraization V s t hs ht c) :
    ∃ f : K.sheaf ⟶ L.sheaf, ∀ i,
      f.over (A.regularOpen i) = Intrinsic.RegularMapGluing.nativeFramedRegularMap V K L (A.regularOpen i)
        (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1)) inf_le_right inf_le_left
        (A.regularCoefficient i) := by
  apply Intrinsic.RegularMapGluing.exists_morphism_of_native_regular_coefficients V K L A.regularOpen A.regularOpen_covers
    (fun i => SectionLocalFrames.sectionLocalFrame (t i.2)) (fun i => SectionLocalFrames.sectionLocalFrame (s i.1))
    (fun _ => inf_le_right) (fun _ => inf_le_left) A.regularCoefficient
  intro i j x hi hj
  have hL := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_ratio V.presentation s hs i.1 j.1 x hi.1).trans
    (SectionFrameEvaluation.sectionFrame_pointTransition V.presentation (s i.1) (s j.1) x hi.1 hj.1).symm
  have hK := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_ratio V.presentation t ht i.2 j.2 x hi.2).trans
    (SectionFrameEvaluation.sectionFrame_pointTransition V.presentation (t i.2) (t j.2) x hi.2 hj.2).symm
  rw [← hL, ← hK, A.regularCoefficient_value i x hi, A.regularCoefficient_value j x hj]
  exact (hc i j x hi hj).symm.trans (mul_comm _ _)

end

include hs ht hc in
theorem GeneratedHolomorphicMorphisms.generated_holomorphicMorphism_algebraization :
    ∃ A : SectionGraphNe.SectionGraphAlgebraization V s t hs ht c,
      Nonempty (SectionGraphNe.SectionGraphAlgebraization.AlgebraicMorphism V s t hs ht c A) := by
  obtain ⟨A⟩ := SectionGraphNe.sectionGraphAlgebraization_nonempty V s t hs ht c hc
  obtain ⟨f, hf⟩ := A.exists_algebraicMorphism V s t hs ht c hc
  exact ⟨A, ⟨⟨f, hf⟩⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
