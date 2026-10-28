import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveCover

/-! # Positive Transitivity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveTransitivity

noncomputable section

/-! Canonical positive-degree comparisons of affine covers compose
without a choice of refinement. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι κ τ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens) (W : τ → X.left.Opens)
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤) (hW : ⨆ i, W i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i)) (haW : ∀ i, IsAffineOpen (W i))
  (M : X.left.Modules) [M.IsQuasicoherent] (g : ℕ) (hg : 0 < g)

theorem hom_comp :
    (PositiveCover.Comparison.iso R X U V hU hV haU haV M g hg).hom ≫
        (PositiveCover.Comparison.iso R X V W hV hW haV haW M g hg).hom =
      (PositiveCover.Comparison.iso R X U W hU hW haU haW M g hg).hom := by
  cases g with
  | zero => exact (Nat.lt_irrefl 0 hg).elim
  | succ n =>
      simp only [PositiveCover.Comparison.iso, Cover.Comparison.iso,
        Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

theorem hom_inv :
    (PositiveCover.Comparison.iso R X U W hU hW haU haW M g hg).hom ≫
        (PositiveCover.Comparison.iso R X V W hV hW haV haW M g hg).inv =
      (PositiveCover.Comparison.iso R X U V hU hV haU haV M g hg).hom := by
  rw [← hom_comp R X U V W hU hV hW haU haV haW M g hg, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem inv_hom :
    (PositiveCover.Comparison.iso R X U V hU hV haU haV M g hg).inv ≫
        (PositiveCover.Comparison.iso R X U W hU hW haU haW M g hg).hom =
      (PositiveCover.Comparison.iso R X V W hV hW haV haW M g hg).hom := by
  rw [← hom_comp R X U V W hU hV hW haU haV haW M g hg, Iso.inv_hom_id_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveTransitivity
