import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameRigidity
import OAI.RepresentationTheory.Theta.Geometric.Local.BaseChangeFrames

/-! # Relative Local Frames -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalFrames.Geometric

noncomputable section

/-! A normalized section on a local base change of the actual varying
projective family is a frame when its original closed-fiber line is
trivial. Properness and the universal function comparison are derived. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.Local.BaseChangeFrames

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S)

include P hs in
theorem relativeProjective_localBaseChange_normalizedSection_isIso
    {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
    (f : Y ⟶ X.left) (ρ : Y ⟶ Spec (.of R)) (g : Spec (.of R) ⟶ S)
    (hp : IsPullback f ρ X.hom g)
    (b : Spec (.of R) ⟶ Y) (hb : b ≫ ρ = 𝟙 _)
    (h : b ≫ f = g ≫ s) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj L.sheaf)
    (hv : (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h L.sheaf r).hom.app ⊤
      (FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj L.sheaf)
        (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ v)) = (1 : Γ(Spec (.of R), ⊤)))
    (e : (Scheme.Modules.pullback (X.hom.fiberι (g (IsLocalRing.closedPoint R)))).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (X.hom.fiber (g (IsLocalRing.closedPoint R)))) : IsIso v := by
  let : IsProper ρ := MorphismProperty.of_isPullback (P := @IsProper) hp inferInstance
  let x := IsLocalRing.closedPoint R
  let f₀ := ρ.fiberι x
  let ρ₀ := ρ.fiberToSpecResidueField x
  let g₀ := (Spec (.of R)).fromSpecResidueField x
  have hp₀ : IsPullback f₀ ρ₀ ρ g₀ := IsPullback.of_hasPullback ρ g₀
  let b₀ := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f₀ ρ₀ ρ g₀ hp₀ b hb
  have hb₀ := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f₀ ρ₀ ρ g₀ hp₀ b hb
  have hx₀ := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f₀ ρ₀ ρ g₀ hp₀ b hb
  let : IsIso ρ₀.appTop :=
    AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions.projectivePresentation_baseChange_globalFunctions_isIso P s hs (hp₀.paste_horiz hp)
  let : IsIso b₀.appTop := FormalGeometry.Completion.Frame.AxisRigidity.Construction.section_appTop_isIso ρ₀ b₀ hb₀
  let r' := FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h L.sheaf r
  exact RepresentationTheory.Theta.Geometric.Normalized.ClosedFiberFrames.normalizedClosedFiberSection_isIso ρ (L.pullback f) v b₀
    (RepresentationTheory.Theta.Geometric.FiberLineTrivialityPullback.fiberTrivializationPullback f ρ X.hom g hp.w x L.sheaf e)
    (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f₀ b₀ g₀ b hx₀ (L.pullback f).sheaf r')
    (RepresentationTheory.Theta.Geometric.Normalized.SectionPullback.normalizedSection_pullback f₀ b₀ g₀ b hx₀ (L.pullback f).sheaf r' v hv)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalFrames.Geometric
