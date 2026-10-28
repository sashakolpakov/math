import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RestrictionComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

/-! # Restriction Square -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RestrictionSquare

noncomputable section

/-! Evaluating a contracted actual line formula along an arbitrary lifted test point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

theorem contraction_square {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ g = q) {M N P : Z.Modules}
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj M) :
    (Scheme.Modules.pullback f).map (Contraction.contractLeft (BilinearPullback.pullback g hM hN β) s) ≫
        ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).app P).hom =
      ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).app N).hom ≫
        Contraction.contractLeft (BilinearPullback.pullback q hM hN β)
          (ContractionPullback.pulledSection f s ≫ ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).app M).hom) := by
  subst q
  change (Scheme.Modules.pullback f).map (Contraction.contractLeft (BilinearPullback.pullback g hM hN β) s) ≫
      (((Scheme.Modules.pullbackComp f g).app P) ≪≫ Iso.refl _).hom =
    (((Scheme.Modules.pullbackComp f g).app N) ≪≫ Iso.refl _).hom ≫
      Contraction.contractLeft (BilinearPullback.pullback (f ≫ g) hM hN β)
        (ContractionPullback.pulledSection f s ≫ (((Scheme.Modules.pullbackComp f g).app M) ≪≫ Iso.refl _).hom)
  simp only [Iso.trans_refl]
  exact RestrictionComposition.contraction_comp f g hM hN β s

variable {S : Scheme.{u}} {K E : Over S} (p : K ⟶ E)
  (M N P : Line.Bundles.LineBundle E.left) (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf P.sheaf)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ (Scheme.Modules.pullback p.left).obj M.sheaf)

/-- The evaluated section is the existing canonical fiber frame, so the formula applies on every
test scheme with its exact geometric line identifications. -/
theorem frame_evaluation {T : Over S} (a : T ⟶ K) (q : T ⟶ E) (h : a ≫ p = q) :
    (Scheme.Modules.pullback a.left).map (Contraction.contractLeft (BilinearPullback.pullback p.left M.isLine N.isLine β) s.hom) ≫
        (Line.Fibers.fiberPullbackIso P a p q h).hom =
      (Line.Fibers.fiberPullbackIso N a p q h).hom ≫
        Contraction.contractLeft (BilinearPullback.pullback q.left M.isLine N.isLine β)
          (GlobalPullbackFrame.atPoint p M s a q h).hom := by
  have he := contraction_square a.left p.left q.left (congrArg Over.Hom.left h)
    M.isLine N.isLine β s.hom
  rw [GlobalPullbackFrame.atPoint, GlobalPullbackFrame.comparison_eq]
  exact he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RestrictionSquare
