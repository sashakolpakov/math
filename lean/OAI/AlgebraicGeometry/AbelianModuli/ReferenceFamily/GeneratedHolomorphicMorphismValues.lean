import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GeneratedHolomorphicMorphisms
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularMapCoordinates

/-! # Generated Holomorphic Morphism Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The algebraized generated-line morphism has precisely the given
native coefficient at every point of the original common frame cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    {s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf)}
    {t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf)}
    {hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)}
    {ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j)}
    {c : ∀ i, DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := SectionComparisonGauges.sectionComparisonOpen V s t i)}
    {A : SectionGraphNe.SectionGraphAlgebraization V s t hs ht c}
    (B : SectionGraphNe.SectionGraphAlgebraization.AlgebraicMorphism V s t hs ht c A)

theorem SectionGraphNe.SectionGraphAlgebraization.AlgebraicMorphism.coefficient (i : Fin (n + 1) × Fin (m + 1)) :
    LineFrameAtlas.lineMorphismCoefficient B.map (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1))
      (A.regularOpen i) inf_le_right inf_le_left = A.regularCoefficient i :=
  Intrinsic.RegularMapCoordinates.lineMorphismCoefficient_of_nativeFramedRegularMap V K L B.map (A.regularOpen i)
    (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1)) inf_le_right inf_le_left
    (A.regularCoefficient i) (B.map_local i)

theorem SectionGraphNe.SectionGraphAlgebraization.AlgebraicMorphism.coefficient_value (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i) :
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (A.regularOpen i) hi
      (LineFrameAtlas.lineMorphismCoefficient B.map (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (s i.1))
        (A.regularOpen i) inf_le_right inf_le_left) = c i ⟨x, hi⟩ :=
  (congrArg (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (A.regularOpen i) hi) (B.coefficient i)).trans
    (A.regularCoefficient_value i x hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
