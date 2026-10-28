import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoStalkSections
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameClassification

/-! # Stalk Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.StalkFrames.Theta.Geometric

noncomputable section

/-! Actual frames over every base local ring glue to a global normalized
frame on a smooth projective connected family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoStalkSections

variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    [IsNoetherianRing Γ(S, ⊤)]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X)
    (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S) (L : Line.Bundles.LineBundle X.left)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ Line.Bundles.structureModule S)

include P s hs r in
theorem projective_line_trivial_of_stalk_frames
    (hL : ∀ x : S, Nonempty ((L.pullback
      (pullback.fst X.hom (S.fromSpecStalk x))).sheaf ≅
        Line.Bundles.structureModule (pullback X.hom (S.fromSpecStalk x)))) :
    Nonempty (L.sheaf ≅ Line.Bundles.structureModule X.left) := by
  let D := FormalGeometry.Completion.Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L
  let : Mono (D.rigidifiedFrameScheme s hs r).hom :=
    Picard.ThetaConstruction.RelativeFrameRigidity.Geometric.relativeProjective_rigidifiedFrame_mono P s hs D r
  let : IsIso (D.rigidifiedFrameScheme s hs r).hom :=
    MonoStalkSections.mono_isIso_of_stalk_sections _ (by
      intro x
      obtain ⟨e⟩ := hL x
      obtain ⟨v⟩ := Picard.ThetaConstruction.RelativeFrameClassification.Geometric.relativeProjective_rigidifiedFrame_hasPoint_of_trivialization P s hs D r
        (pullback.fst X.hom (S.fromSpecStalk x))
        (pullback.snd X.hom (S.fromSpecStalk x)) (S.fromSpecStalk x)
        (IsPullback.of_hasPullback X.hom (S.fromSpecStalk x)) e.symm
      exact ⟨v.left, v.w⟩)
  let v : Over.mk (𝟙 S) ⟶ D.rigidifiedFrameScheme s hs r :=
    Over.homMk (inv (D.rigidifiedFrameScheme s hs r).hom) (IsIso.inv_hom_id _)
  have hc := (Picard.ThetaConstruction.RelativeFrameClassification.Geometric.relativeProjective_rigidifiedFrame_hasPoint_iff_trivialClass P s hs D r
    (𝟙 X.left) X.hom (𝟙 S) IsPullback.of_id_fst).mp ⟨v⟩
  rw [Line.Bundles.LineBundle.pullbackClass_id] at hc
  exact Quotient.exact hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.StalkFrames.Theta.Geometric
