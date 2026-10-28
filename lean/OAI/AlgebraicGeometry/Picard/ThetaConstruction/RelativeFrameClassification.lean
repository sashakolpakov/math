import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameRigidity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalNormalizedFrameClassification
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.RigidifiedFrames

/-! # Relative Frame Classification -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameClassification.Geometric

noncomputable section

/-! The normalized-frame scheme of a varying projective family detects
actual triviality on every test scheme, including nonreduced tests. Its
existence and uniqueness follow from the original projective model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.RigidifiedFrames.Construction

universe u
variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S)
    {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left} (D : FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation X.hom L.sheaf)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

include P in
theorem relativeProjective_rigidifiedFrame_hasPoint_of_trivialization
    {Y T : Scheme.{u}} (f : Y ⟶ X.left) (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ X.hom g)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    Nonempty (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) := by
  let : Mono (D.rigidifiedFrameScheme s hs r).hom :=
    RelativeFrameRigidity.Geometric.relativeProjective_rigidifiedFrame_mono P s hs D r
  apply FormalGeometry.Completion.MonomorphismLocalLifts.Construction.mono_hasLift_of_openCover _ (Over.mk g) T.affineCover
  intro i
  let j := pullback.fst ρ (T.affineCover.f i)
  let τ := pullback.snd ρ (T.affineCover.f i)
  let ho : IsPullback (j ≫ f) τ X.hom (T.affineCover.f i ≫ g) :=
    (IsPullback.of_hasPullback ρ (T.affineCover.f i)).paste_horiz hp
  let b := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection (j ≫ f) τ X.hom (T.affineCover.f i ≫ g) ho s hs
  let hb := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd (j ≫ f) τ X.hom (T.affineCover.f i ≫ g) ho s hs
  let hx := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst (j ≫ f) τ X.hom (T.affineCover.f i ≫ g) ho s hs
  let e' := FormalGeometry.Completion.Frame.SchemeNaturality.Construction.compositeLineFrameIso f j L.sheaf e
  exact ⟨D.rigidifiedTrivializationPointEquiv (j ≫ f) τ (T.affineCover.f i ≫ g) ho s hs r
    ⟨FormalGeometry.Completion.Frame.Normalization.Construction.normalizedFrame (j ≫ f) τ b (T.affineCover.f i ≫ g) s hx L.sheaf r e',
      FormalGeometry.Completion.Frame.Normalization.Construction.normalizedFrame_scalar (j ≫ f) τ b hb (T.affineCover.f i ≫ g) s hx L.sheaf r e'⟩⟩

include P in
theorem relativeProjective_rigidifiedFrame_hasPoint_iff_trivialClass
    {Y T : Scheme.{u}} (f : Y ⟶ X.left) (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ X.hom g) :
    Nonempty (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass Y := by
  constructor
  · rintro ⟨v⟩
    exact Quotient.sound ⟨(D.rigidifiedFrameToNormalizedTrivialization f ρ g hp s hs r v).val.symm⟩
  · intro h
    obtain ⟨e⟩ := Quotient.exact h
    exact relativeProjective_rigidifiedFrame_hasPoint_of_trivialization P s hs D r f ρ g hp e.symm

variable [IsNoetherianRing Γ(S, ⊤)] [Flat X.hom]

theorem relativeProjective_projectiveRigidifiedFrame_mono :
    Mono (FormalGeometry.Completion.Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme X P L s hs r).hom :=
  RelativeFrameRigidity.Geometric.relativeProjective_rigidifiedFrame_mono P s hs (FormalGeometry.Completion.Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L) r

theorem relativeProjective_projectiveRigidifiedFrame_hasPoint_iff_trivialClass
    {Y T : Scheme.{u}} (f : Y ⟶ X.left) (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ X.hom g) :
    Nonempty (Over.mk g ⟶ FormalGeometry.Completion.Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme X P L s hs r) ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass Y :=
  relativeProjective_rigidifiedFrame_hasPoint_iff_trivialClass P s hs
    (FormalGeometry.Completion.Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L) r f ρ g hp

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameClassification.Geometric
