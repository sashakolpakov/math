import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FiberComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackSwap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SwapNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

/-! # External Tensor Point Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ExternalTensorPointSymmetry

noncomputable section

/-! The external tensor symmetry acts on every pair of actual test fibers by exchanging the two factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

theorem swap_iso_natural {X : Scheme.{u}} {M M' N N' : X.Modules} (a : M ≅ M') (b : N ≅ N') :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M' N' =
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr b a := by
  apply Iso.ext
  simp only [Iso.trans_hom, Tensor.CongrMapComparison.congr_hom]
  exact Tensor.SwapNaturality.swap_natural a.hom b.hom

theorem pullback_swapped_factors {X Y : Scheme.{u}} (q : X ⟶ Y) (M N : Y.Modules)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) {M' N' : X.Modules}
    (a : (Scheme.Modules.pullback q).obj M ≅ M') (b : (Scheme.Modules.pullback q).obj N ≅ N') :
    (Scheme.Modules.pullback q).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N) ≪≫
      Tensor.LinePullback.pullbackIso q N M hN hM ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr b a =
    Tensor.LinePullback.pullbackIso q M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M' N' := by
  rw [← Iso.trans_assoc, Tensor.PullbackSwap.iso_swap, Iso.trans_assoc, ← swap_iso_natural]

theorem swap_path {C : Type*} [Category C] {A B D E F G : C}
    (c : A ≅ B) (f : A ≅ D) (k : D ≅ E) (g : B ≅ E)
    (r : D ≅ G) (b : G ≅ F) (d : B ≅ F) {H : C} (v : F ≅ H)
    (w : E ≅ H) (hg : g = c.symm ≪≫ f ≪≫ k)
    (hs : k ≪≫ w = r ≪≫ b ≪≫ v) (hc : f ≪≫ r ≪≫ b = c ≪≫ d) :
    g ≪≫ w = d ≪≫ v := by
  rw [hg]
  calc
    (c.symm ≪≫ f ≪≫ k) ≪≫ w = c.symm ≪≫ f ≪≫ (k ≪≫ w) := by simp only [Iso.trans_assoc]
    _ = c.symm ≪≫ f ≪≫ (r ≪≫ b ≪≫ v) := congrArg (fun e => c.symm ≪≫ f ≪≫ e) hs
    _ = c.symm ≪≫ (f ≪≫ r ≪≫ b) ≪≫ v := by simp only [Iso.trans_assoc]
    _ = c.symm ≪≫ (c ≪≫ d) ≪≫ v := congrArg (fun e => c.symm ≪≫ e ≪≫ v) hc
    _ = d ≪≫ v := by simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

variable {S : Scheme.{u}} (A : Over S) (L : Line.Bundles.LineBundle A.left)

theorem symmetry_eq : ExternalTensorSymmetry.symmetry A L =
    Tensor.FiberComposition.comparison L (fst A A) (snd A A) (β_ A A).hom (snd A A) (fst A A)
      (braiding_hom_fst A A) (braiding_hom_snd A A) ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L (snd A A)) (Line.Fibers.fiber L (fst A A)) :=
  (Iso.trans_assoc (Tensor.LinePullback.pullbackIso (β_ A A).hom.left _ _ (Line.Fibers.fiber_isLine L (fst A A)) (Line.Fibers.fiber_isLine L (snd A A)))
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (ExternalTensorSymmetry.firstIso A L) (ExternalTensorSymmetry.secondIso A L))
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L (snd A A)) (Line.Fibers.fiber L (fst A A)))).symm

/-- Evaluate the actual external tensor symmetry using the specified individual fiber coordinates. -/
theorem atPoint {T : Over S} (q : T ⟶ A ⊗ A) (x y : T ⟶ A)
    (hx : q ≫ fst A A = x) (hy : q ≫ snd A A = y)
    (hx' : (q ≫ (β_ A A).hom) ≫ fst A A = y)
    (hy' : (q ≫ (β_ A A).hom) ≫ snd A A = x) :
    Line.SymmetryFibers.atPoint (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L))
        (β_ A A).hom (ExternalTensorSymmetry.symmetry A L) q ≪≫
      Tensor.FiberComposition.comparison L (fst A A) (snd A A) q x y hx hy =
    Tensor.FiberComposition.comparison L (fst A A) (snd A A) (q ≫ (β_ A A).hom) y x hx' hy' ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L y) (Line.Fibers.fiber L x) := by
  let f := (Scheme.Modules.pullback q.left).mapIso
    (Tensor.FiberComposition.comparison L (fst A A) (snd A A) (β_ A A).hom (snd A A) (fst A A)
      (braiding_hom_fst A A) (braiding_hom_snd A A))
  let c := (Scheme.Modules.pullbackComp q.left (β_ A A).hom.left).app
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L (fst A A)) (Line.Fibers.fiber L (snd A A)))
  let r := Tensor.LinePullback.pullbackIso q.left (Line.Fibers.fiber L (snd A A)) (Line.Fibers.fiber L (fst A A))
    (Line.Fibers.fiber_isLine L (snd A A)) (Line.Fibers.fiber_isLine L (fst A A))
  let b := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.Fibers.fiberPullbackIso L q (snd A A) y hy) (Line.Fibers.fiberPullbackIso L q (fst A A) x hx)
  let d := Tensor.FiberComposition.comparison L (fst A A) (snd A A) (q ≫ (β_ A A).hom) y x hx' hy'
  let v := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L y) (Line.Fibers.fiber L x)
  have hc : f ≪≫ r ≪≫ b = c ≪≫ d :=
    Tensor.FiberComposition.composition L (fst A A) (snd A A) (β_ A A).hom q (snd A A) (fst A A)
      (braiding_hom_fst A A) (braiding_hom_snd A A) y x hy hx hx' hy'
  have hs := pullback_swapped_factors q.left (Line.Fibers.fiber L (snd A A)) (Line.Fibers.fiber L (fst A A))
    (Line.Fibers.fiber_isLine L (snd A A)) (Line.Fibers.fiber_isLine L (fst A A))
    (Line.Fibers.fiberPullbackIso L q (snd A A) y hy) (Line.Fibers.fiberPullbackIso L q (fst A A) x hx)
  let k := (Scheme.Modules.pullback q.left).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L (snd A A)) (Line.Fibers.fiber L (fst A A)))
  let w := Tensor.FiberComposition.comparison L (fst A A) (snd A A) q x y hx hy
  let g := Line.SymmetryFibers.atPoint (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L))
    (β_ A A).hom (ExternalTensorSymmetry.symmetry A L) q
  have he : (Scheme.Modules.pullback q.left).mapIso (ExternalTensorSymmetry.symmetry A L) = f ≪≫ k :=
    (congrArg ((Scheme.Modules.pullback q.left).mapIso) (symmetry_eq A L)).trans
      (Functor.mapIso_trans (Scheme.Modules.pullback q.left) _ _)
  have hg : g = c.symm ≪≫ f ≪≫ k :=
    (Line.SymmetryFibers.atPoint_eq (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L))
      (β_ A A).hom (ExternalTensorSymmetry.symmetry A L) q).trans
      (congrArg (fun e => c.symm ≪≫ e) he)
  exact swap_path c f k g r b d v w hg hs hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ExternalTensorPointSymmetry
