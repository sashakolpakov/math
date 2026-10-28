import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProductCoordinates

/-! # Witt Tuple Reduction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReductionCoordinates

noncomputable section

/-! Canonical Witt tuple reduction commutes with the original frame projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReduction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X)

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem iso_projection (b : Fin (a + 1)) : (WittTupleReduction.iso p k X n m hnm a t).hom ≫
    (WittTupleReduction.reduction p k X n m).map (Pi.π (fun b => WittFrameFamily.Family.frame p k X m (t b)) b) =
      Pi.π (fun b => WittFrameFamily.Family.frame p k X n (t b)) b ≫ (WittFrameReduction.iso p k X n m hnm (t b)).hom :=
  ProductCoordinates.Comparison.projection (WittTupleReduction.reduction p k X n m) (fun b => WittFrameFamily.Family.frame p k X m (t b))
    (fun b => WittFrameFamily.Family.frame p k X n (t b)) (fun b => WittFrameReduction.iso p k X n m hnm (t b)) b

theorem morphism_projection (b : Fin (a + 1)) : WittTupleReduction.morphism p k X n m hnm a t ≫
    (Pi.π (fun b => WittFrameFamily.Family.frame p k X m (t b)) b).hom =
      (Pi.π (fun b => WittFrameFamily.Family.frame p k X n (t b)) b).hom ≫ WittFrameReduction.morphism p k X n m hnm (t b) := by
  let L := BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n
  have he : (WittTupleReduction.iso p k X n m hnm a t).hom.hom ≫
      ((WittTupleReduction.reduction p k X n m).map (Pi.π (fun b => WittFrameFamily.Family.frame p k X m (t b)) b)).hom =
        (Pi.π (fun b => WittFrameFamily.Family.frame p k X n (t b)) b).hom ≫
          (WittFrameReduction.iso p k X n m hnm (t b)).hom.hom :=
    (L.map_comp _ _).symm.trans
      ((congrArg L.map (iso_projection p k X n m hnm a t b)).trans (L.map_comp _ _))
  have hn := Crystalline.LevelReductionFunctor.map_comp_hom n
    (Pi.π (fun b => WittFrameFamily.Family.frame p k X m (t b)) b).hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun c => (WittTupleReduction.iso p k X n m hnm a t).hom.hom ≫ c) hn.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun c => c ≫ Crystalline.LevelReduction.hom n (WittFrameFamily.Family.frame p k X m (t b)).obj) he).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun c => (Pi.π (fun b => WittFrameFamily.Family.frame p k X n (t b)) b).hom ≫ c)
              (WittFrameReduction.iso_hom p k X n m hnm (t b)))))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReductionCoordinates
