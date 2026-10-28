import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalNormalizedFrameClassification
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.RigidifiedFrames

/-! # Global Frame Triviality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The normalized-frame scheme detects actual triviality of a line
bundle on every test family, including nonaffine and nonreduced tests. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
section

variable {K : Type u} [Field K] [IsAlgClosed K] {A X S : Scheme.{u}}
  (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
  [IsAffine S] {π : X ⟶ S} [IsProper π]
  (q : X ⟶ A) (tS : S ⟶ Spec (.of K)) (hX : IsPullback q π a tS)
  {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X} (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  {Y T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
  (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
  (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

include hX hp

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrame_hasPoint_iff_trivialization :
    Nonempty (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) ↔
      Nonempty (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨(D.rigidifiedFrameToNormalizedTrivialization f ρ g hp s hs r p).val⟩
  · rintro ⟨e⟩
    exact D.rigidifiedFrame_hasPoint_of_trivialization a q tS hX f ρ g hp s hs r e

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrame_hasPoint_iff_trivialClass :
    Nonempty (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass Y := by
  rw [D.rigidifiedFrame_hasPoint_iff_trivialization a q tS hX f ρ g hp s hs r]
  constructor
  · rintro ⟨e⟩
    exact Quotient.sound ⟨e.symm⟩
  · intro h
    obtain ⟨e⟩ := Quotient.exact h
    exact ⟨e.symm⟩

end

theorem GlobalFrameTriviality.Construction.projectiveLineBundleRigidifiedFrame_hasPoint_iff_trivialClass
    {K : Type u} [Field K] [IsAlgClosed K] {A S : Scheme.{u}}
    (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
    [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]
    (q : X.left ⟶ A) (tS : S ⟶ Spec (.of K)) (hX : IsPullback q X.hom a tS)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    {Y T : Scheme.{u}} (f : Y ⟶ X.left) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ X.hom g) :
    Nonempty (Over.mk g ⟶ Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme X P L s hs r) ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass Y := by
  have : IsProper X.hom := P.proper
  exact (Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).rigidifiedFrame_hasPoint_iff_trivialClass
    a q tS hX f ρ g hp s hs r

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
