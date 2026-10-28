import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TraceRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveTransitivity

/-! # Positive Refinement Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveRefinementRecovery

noncomputable section

/-! Reversing an actual positive-degree cover isomorphism, or making
a full cycle through an actual refinement, returns the original class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι κ ν : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (hU : iSup U = ⊤) (hV : iSup V = ⊤)
  (haU : ∀ j, IsAffineOpen (U j)) (haV : ∀ j, IsAffineOpen (V j))
  (M : X.left.Modules) [M.IsQuasicoherent] (g : ℕ) (hg : 0 < g)

theorem reverse_hom :
    (PositiveCover.Comparison.iso R X U V hU hV haU haV M g hg).hom =
      (PositiveCover.Comparison.iso R X V U hV hU haV haU M g hg).inv := by
  cases g with
  | zero => exact (Nat.lt_irrefl 0 hg).elim
  | succ q => rfl

variable (W : ν → X.left.Opens) (hW : iSup W = ⊤) (haW : ∀ j, IsAffineOpen (W j))
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

theorem cycle :
    (PositiveCover.Comparison.iso R X W U hW hU haW haU M g hg).hom ≫
      (CohomologyNaturality.forgetCoefficients R).map
        (homologyMap (CoverRefinement.map R X U V r M) g) ≫
      (PositiveCover.Comparison.iso R X V W hV hW haV haW M g hg).hom = 𝟙 _ := by
  rw [TraceRefinement.map_eq_positiveCoverIso R X U V r hU hV haU haV M g hg,
    ← Category.assoc,
    PositiveTransitivity.hom_comp R X W U V hW hU hV haW haU haV M g hg,
    reverse_hom R X W V hW hV haW haV M g hg, Iso.inv_hom_id]

theorem cycle_apply (x : (DimensionBound.complex R X M W).homology g) :
    (PositiveCover.Comparison.iso R X V W hV hW haV haW M g hg).hom
      (homologyMap (CoverRefinement.map R X U V r M) g
        ((PositiveCover.Comparison.iso R X W U hW hU haW haU M g hg).hom x)) = x :=
  ConcreteCategory.congr_hom (cycle R X U V hU hV haU haV M g hg W hW haW r) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveRefinementRecovery
