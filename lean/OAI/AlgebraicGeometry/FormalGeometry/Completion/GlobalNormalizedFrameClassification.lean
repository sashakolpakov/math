import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameMonomorphism
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameUniversal
import OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismLocalLifts

/-! # Global Normalized Frame Classification -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The normalized-frame scheme classifies actual normalized frames on
arbitrary test schemes of a proper integral constant family. Existence
is obtained by gluing affine classifiers, and uniqueness is geometric. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {A X S : Scheme.{u}}
  (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
  [IsAffine S] {π : X ⟶ S} [IsProper π]
  (q : X ⟶ A) (tS : S ⟶ Spec (.of K)) (hX : IsPullback q π a tS)
  {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X} (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  {Y T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
  (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
  (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

include hX hp

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrame_hasPoint_of_trivialization
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    Nonempty (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) := by
  have : Mono (D.rigidifiedFrameScheme s hs r).hom := D.rigidifiedFrame_mono a q tS hX s hs r
  apply MonomorphismLocalLifts.Construction.mono_hasLift_of_openCover _ (Over.mk g) T.affineCover
  intro i
  let j := pullback.fst ρ (T.affineCover.f i)
  let τ := pullback.snd ρ (T.affineCover.f i)
  let ho : IsPullback (j ≫ f) τ π (T.affineCover.f i ≫ g) :=
    (IsPullback.of_hasPullback ρ (T.affineCover.f i)).paste_horiz hp
  let b := NormalizedFrameClassification.Construction.cartesianSection (j ≫ f) τ π (T.affineCover.f i ≫ g) ho s hs
  let hb := NormalizedFrameClassification.Construction.cartesianSection_snd (j ≫ f) τ π (T.affineCover.f i ≫ g) ho s hs
  let hx := NormalizedFrameClassification.Construction.cartesianSection_fst (j ≫ f) τ π (T.affineCover.f i ≫ g) ho s hs
  let e' := Frame.SchemeNaturality.Construction.compositeLineFrameIso f j L.sheaf e
  exact ⟨D.rigidifiedTrivializationPointEquiv (j ≫ f) τ (T.affineCover.f i ≫ g) ho s hs r
    ⟨Frame.Normalization.Construction.normalizedFrame (j ≫ f) τ b (T.affineCover.f i ≫ g) s hx L.sheaf r e',
      Frame.Normalization.Construction.normalizedFrame_scalar (j ≫ f) τ b hb (T.affineCover.f i ≫ g) s hx L.sheaf r e'⟩⟩

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.globalRigidifiedTrivializationPointEquiv :
    { e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf //
      Rigidified.FrameScalar.Construction.frameAxisScalar f (NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs) g s
        (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs) L.sheaf r e = 1 } ≃
      (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) := by
  haveI : Mono (D.rigidifiedFrameScheme s hs r).hom := D.rigidifiedFrame_mono a q tS hX s hs r
  haveI : Subsingleton (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) := ⟨fun v w => by
    apply Over.OverMorphism.ext
    exact (cancel_mono (D.rigidifiedFrameScheme s hs r).hom).mp (v.w.trans w.w.symm)⟩
  have he : ∀ e e' : { e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf //
      Rigidified.FrameScalar.Construction.frameAxisScalar f (NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs) g s
        (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs) L.sheaf r e = 1 }, e = e' := by
    intro e e'
    apply Subtype.ext
    exact ConstantFamilyFrameRigidity.Construction.properConstantFamily_normalizedFrame_unique a (f ≫ q) ρ (g ≫ tS) (hp.paste_horiz hX)
      f (NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs) (NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π g hp s hs)
      g s (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs) L.sheaf r e.val e'.val e.property e'.property
  refine (Equiv.ofBijective (D.rigidifiedFrameToNormalizedTrivialization f ρ g hp s hs r) ⟨?_, ?_⟩).symm
  · intro v w _
    exact Subsingleton.elim v w
  · intro e
    obtain ⟨v⟩ := D.rigidifiedFrame_hasPoint_of_trivialization a q tS hX f ρ g hp s hs r e.val
    exact ⟨v, he _ _⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
