import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.KernelPair
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OpenInvariant

/-! # Kernel Pair Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.KernelPairRestriction

noncomputable section

/-!
# Ordinary descent invariants restrict on actual scheme kernel pairs
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
  (h : iX ≫ f = f' ≫ iY) (hpre : f ⁻¹ᵁ iY.opensRange ≤ iX.opensRange)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- Restriction preserves the ordinary invariant constructed on the actual scheme kernel pair. -/
def invariantIso :
    (Scheme.Modules.restrictFunctor iY).obj (Geometric.CechInvariant.ordinaryInvariantSheaf f D) ≅
      Geometric.CechInvariant.ordinaryInvariantSheaf f' (SquareGluing.pulledDatum f f' iX iY h D) :=
  OpenInvariant.invariantIso f (pullback.fst f f) (pullback.snd f f) pullback.condition
    f' (pullback.fst f' f') (pullback.snd f' f') pullback.condition iY iX
    (Open.KernelPair.map f f' iX iY h) h (Open.KernelPair.map_fst f f' iX iY h)
    (Open.KernelPair.map_snd f f' iX iY h) D hpre
    (Open.KernelPair.second_preimage_le f f' iX iY h hpre)

include hpre in
/-- Ordinary local effectivity detects the actual restricted global comparison. -/
theorem comparison_restrict_isIso_iff :
    IsIso ((Scheme.Modules.restrictFunctor iX).map (Geometric.CechInvariant.ordinaryComparison f D)) ↔
      IsIso (Geometric.CechInvariant.ordinaryComparison f' (SquareGluing.pulledDatum f f' iX iY h D)) :=
  OpenInvariant.comparison_map_isIso_iff f (pullback.fst f f) (pullback.snd f f)
    pullback.condition f' (pullback.fst f' f') (pullback.snd f' f') pullback.condition iY iX
    (Open.KernelPair.map f f' iX iY h) h (Open.KernelPair.map_fst f f' iX iY h)
    (Open.KernelPair.map_snd f f' iX iY h) D hpre
    (Open.KernelPair.second_preimage_le f f' iX iY h hpre)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.KernelPairRestriction
