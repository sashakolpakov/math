import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ComparisonPaths
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

/-! # Pullback Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackGluing

noncomputable section

/-!
# The canonical tensor comparison respects standard geometric descent gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

/-- Tensoring actual line-fiber isomorphisms preserves composition in both factors. -/
theorem tensorIso_trans {T : Scheme.{u}} {M N P M' N' P' : T.Modules}
    (a : M ≅ N) (b : M' ≅ N') (c : N ≅ P) (d : N' ≅ P') :
    UnitPullback.tensorIso a b ≪≫ UnitPullback.tensorIso c d = UnitPullback.tensorIso (a ≪≫ c) (b ≪≫ d) := by
  apply Iso.ext
  exact SheafMaps.tensorMap_comp a.hom b.hom c.hom d.hom

/-- The tensor map of a conjugated comparison cancels the same starting comparison in both factors. -/
theorem tensorIso_path {T : Scheme.{u}} {M N P Q M' N' P' Q' : T.Modules}
    (a : M ≅ N) (b : M' ≅ N') (c : N ≅ P) (d : N' ≅ P') (e : Q ≅ P) (f : Q' ≅ P') :
    UnitPullback.tensorIso a.symm b.symm ≪≫ UnitPullback.tensorIso (a ≪≫ c ≪≫ e.symm) (b ≪≫ d ≪≫ f.symm) =
      UnitPullback.tensorIso c d ≪≫ UnitPullback.tensorIso e.symm f.symm := by
  rw [tensorIso_trans, tensorIso_trans]
  congr 1 <;> simp only [Iso.symm_self_id_assoc]

/-- Cancellation of an actual isomorphism also holds for whole isomorphism paths. -/
theorem cancel_left {C : Type*} [Category C] {M N P : C} (a : M ≅ N) {b c : N ≅ P}
    (h : a ≪≫ b = a ≪≫ c) : b = c := by
  apply Iso.ext
  exact (cancel_epi a.hom).mp (congrArg Iso.hom h)

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  (M N : Y.Modules) (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)

/-- The tensor comparison for two consecutive actual geometric pullbacks. -/
def iterated :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback f).obj M))
        ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback f).obj N)) :=
  (Scheme.Modules.pullback p).mapIso (LinePullback.pullbackIso f M N hM hN) ≪≫
    LinePullback.pullbackIso p ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
      (hM.pullback f) (hN.pullback f)

/-- The iterated comparison has its exact geometric composition path. -/
theorem iterated_comp :
    (Scheme.Modules.pullbackComp p f).symm.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ iterated f p M N hM hN =
      LinePullback.pullbackIso (p ≫ f) M N hM hN ≪≫
        UnitPullback.tensorIso ((Scheme.Modules.pullbackComp p f).symm.app M) ((Scheme.Modules.pullbackComp p f).symm.app N) := by
  unfold iterated
  rw [← Iso.trans_assoc]
  exact (ComparisonPaths.composition_iso p f M N hM hN).symm

/-- The actual tensor comparison intertwines the standard kernel-pair gluing of both input lines. -/
theorem gluing_iso :
    iterated f p M N hM hN ≪≫ UnitPullback.tensorIso ((Cech.MateNormalization.standardGluing f p q h).app M)
      ((Cech.MateNormalization.standardGluing f p q h).app N) =
    (Cech.MateNormalization.standardGluing f p q h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ iterated f q M N hM hN := by
  apply cancel_left ((Scheme.Modules.pullbackComp p f).symm.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N))
  rw [← Iso.trans_assoc, iterated_comp, Iso.trans_assoc]
  change LinePullback.pullbackIso (p ≫ f) M N hM hN ≪≫
      (UnitPullback.tensorIso ((Scheme.Modules.pullbackComp p f).app M).symm ((Scheme.Modules.pullbackComp p f).app N).symm ≪≫
        UnitPullback.tensorIso (((Scheme.Modules.pullbackComp p f).app M) ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
          ((Scheme.Modules.pullbackComp q f).app M).symm)
          (((Scheme.Modules.pullbackComp p f).app N) ≪≫ (Scheme.Modules.pullbackCongr h).app N ≪≫
          ((Scheme.Modules.pullbackComp q f).app N).symm)) = _
  rw [tensorIso_path, ← Iso.trans_assoc, ← ComparisonPaths.congr_iso h M N hM hN, Iso.trans_assoc]
  change (Scheme.Modules.pullbackCongr h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫
    (LinePullback.pullbackIso (q ≫ f) M N hM hN ≪≫
      UnitPullback.tensorIso ((Scheme.Modules.pullbackComp q f).symm.app M) ((Scheme.Modules.pullbackComp q f).symm.app N)) = _
  rw [← iterated_comp]
  change (Scheme.Modules.pullbackCongr h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫
      ((Scheme.Modules.pullbackComp q f).symm.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ iterated f q M N hM hN) =
    ((Scheme.Modules.pullbackComp p f).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).symm ≪≫
      ((((Scheme.Modules.pullbackComp p f).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)) ≪≫
        (Scheme.Modules.pullbackCongr h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫
        ((Scheme.Modules.pullbackComp q f).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).symm) ≪≫ iterated f q M N hM hN)
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackGluing
