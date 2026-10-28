import OAI.RepresentationTheory.Theta.Geometric.Local.ConstantFamilyFrames
import OAI.RepresentationTheory.Theta.Geometric.FiberLineTrivialityPullback

/-! # Base Change Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.BaseChangeFrames

noncomputable section

/-! Normalized sections become frames after a local base change through
a trivial original fiber. The closed-fiber trivialization is pulled back
through the residue-field square rather than supplied on the new family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

theorem localBaseChange_normalizedSection_isIso
    {K R : Type u} [Field K] [IsAlgClosed K] [CommRing R] [IsLocalRing R]
    {A X Y S : Scheme.{u}} (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
    (π : X ⟶ S) (q : X ⟶ A) (t : S ⟶ Spec (.of K)) (hX : IsPullback q π a t)
    (f : Y ⟶ X) (ρ : Y ⟶ Spec (.of R)) (g : Spec (.of R) ⟶ S)
    (hp : IsPullback f ρ π g)
    (s : S ⟶ X) (b : Spec (.of R) ⟶ Y) (hb : b ≫ ρ = 𝟙 _)
    (h : b ≫ f = g ≫ s) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (v : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj L.sheaf)
    (hv : (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h L.sheaf r).hom.app ⊤
      (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj L.sheaf)
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ v)) = (1 : Γ(Spec (.of R), ⊤)))
    (e : (Scheme.Modules.pullback (π.fiberι (g (IsLocalRing.closedPoint R)))).obj L.sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (g (IsLocalRing.closedPoint R)))) : IsIso v := by
  have hY : IsPullback (f ≫ q) ρ a (g ≫ t) := hp.paste_horiz hX
  have : IsProper ρ := MorphismProperty.of_isPullback (P := @IsProper) hY inferInstance
  exact ConstantFamilyFrames.localConstantFamily_normalizedSection_isIso a ρ (f ≫ q) (g ≫ t) hY b hb
    (L.pullback f) (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h L.sheaf r) v hv
    (FiberLineTrivialityPullback.fiberTrivializationPullback f ρ π g hp.w (IsLocalRing.closedPoint R) L.sheaf e)

end

end OAI.RepresentationTheory.Theta.Geometric.Local.BaseChangeFrames
