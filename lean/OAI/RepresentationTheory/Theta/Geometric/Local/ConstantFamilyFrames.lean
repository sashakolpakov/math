import OAI.RepresentationTheory.Theta.Geometric.Normalized.SectionPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.AxisRigidity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification

/-! # Constant Family Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.ConstantFamilyFrames

noncomputable section

/-! For a proper constant integral family over a local ring, a normalized
section is a frame as soon as its closed-fiber line bundle is trivial. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

theorem localConstantFamily_normalizedSection_isIso
    {K R : Type u} [Field K] [IsAlgClosed K] [CommRing R] [IsLocalRing R]
    {A X : Scheme.{u}} (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
    (π : X ⟶ Spec (.of R)) [IsProper π]
    (q : X ⟶ A) (t : Spec (.of R) ⟶ Spec (.of K)) (hp : IsPullback q π a t)
    (s : Spec (.of R) ⟶ X) (hs : s ≫ π = 𝟙 _)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of R)))
    (v : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)
    (hv : r.hom.app ⊤ (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback s L.sheaf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf v)) =
      (1 : Γ(Spec (.of R), ⊤)))
    (e : (Scheme.Modules.pullback (π.fiberι (IsLocalRing.closedPoint R))).obj L.sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (IsLocalRing.closedPoint R))) : IsIso v := by
  let x := IsLocalRing.closedPoint R
  let f := π.fiberι x
  let ρ := π.fiberToSpecResidueField x
  let g := (Spec (.of R)).fromSpecResidueField x
  have hf : IsPullback f ρ π g := IsPullback.of_hasPullback π g
  let b := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ π g hf s hs
  have hb := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π g hf s hs
  have hx := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hf s hs
  have : IsIso b.appTop := AlgebraicGeometry.FormalGeometry.Completion.Frame.AxisRigidity.Construction.properIntegralProduct_section_appTop_isIso a
    (f ≫ q) ρ (g ≫ t) (hf.paste_horiz hp) b hb
  exact Normalized.ClosedFiberFrames.normalizedClosedFiberSection_isIso π L v b e
    (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s hx L.sheaf r)
    (Normalized.SectionPullback.normalizedSection_pullback f b g s hx L.sheaf r v hv)

end

end OAI.RepresentationTheory.Theta.Geometric.Local.ConstantFamilyFrames
