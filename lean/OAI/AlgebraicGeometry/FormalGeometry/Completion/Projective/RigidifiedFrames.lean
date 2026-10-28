import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameMonomorphism
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleTrivialization

/-! # Rigidified Frames -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.RigidifiedFrames

noncomputable section

/-! Native finite-type normalized-frame schemes and their classification
for flat projective line-bundle families. Properness and the section
model are derived from the projective presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S)
  (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

def projectiveLineBundleRigidifiedFrameScheme : Over S := by
  haveI : IsProper X.hom := P.proper
  exact (LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).rigidifiedFrameScheme s hs r

instance projectiveLineBundleRigidifiedFrameScheme_locallyOfFiniteType :
    LocallyOfFiniteType (projectiveLineBundleRigidifiedFrameScheme X P L s hs r).hom := by
  have : IsProper X.hom := P.proper
  exact (LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).rigidifiedFrameScheme_locallyOfFiniteType s hs r

instance projectiveLineBundleRigidifiedFrameScheme_quasiCompact :
    QuasiCompact (projectiveLineBundleRigidifiedFrameScheme X P L s hs r).hom := by
  have : IsProper X.hom := P.proper
  exact (LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).rigidifiedFrameScheme_quasiCompact s hs r

def projectiveLineBundleRigidifiedTrivializationPointEquiv
    {Y T : Scheme.{u}} [IsAffine T] (f : Y ⟶ X.left) (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ X.hom g) :
    { e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf //
      Rigidified.FrameScalar.Construction.frameAxisScalar f (NormalizedFrameClassification.Construction.cartesianSection f ρ X.hom g hp s hs) g s
        (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ X.hom g hp s hs) L.sheaf r e = 1 } ≃
      (Over.mk g ⟶ projectiveLineBundleRigidifiedFrameScheme X P L s hs r) := by
  haveI : IsProper X.hom := P.proper
  exact (LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).rigidifiedTrivializationPointEquiv f ρ g hp s hs r

theorem projectiveLineBundleRigidifiedFrameScheme_mono
    {K : Type u} [Field K] [IsAlgClosed K] {A : Scheme.{u}}
    (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
    (q : X.left ⟶ A) (tS : S ⟶ Spec (.of K)) (hX : IsPullback q X.hom a tS) :
    Mono (projectiveLineBundleRigidifiedFrameScheme X P L s hs r).hom := by
  have : IsProper X.hom := P.proper
  exact (LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).rigidifiedFrame_mono a q tS hX s hs r

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.RigidifiedFrames
