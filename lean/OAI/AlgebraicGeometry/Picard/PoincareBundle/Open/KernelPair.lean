import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareSections
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Kernel Pair -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.KernelPair

noncomputable section

/-!
# The actual scheme kernel pair restricts along a cartesian open square
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
  (h : iX ≫ f = f' ≫ iY)

/-- The induced morphism of actual scheme-theoretic kernel pairs. -/
def map : pullback f' f' ⟶ pullback f f :=
  pullback.map f' f' f f iX iX iY h.symm h.symm

instance map_isOpenImmersion : IsOpenImmersion (KernelPair.map f f' iX iY h) := by
  unfold KernelPair.map
  infer_instance

omit [IsOpenImmersion iX] [IsOpenImmersion iY] in
/-- The first kernel-pair projection commutes with the restriction. -/
theorem map_fst : KernelPair.map f f' iX iY h ≫ pullback.fst f f = pullback.fst f' f' ≫ iX :=
  pullback.lift_fst _ _ _

omit [IsOpenImmersion iX] [IsOpenImmersion iY] in
/-- The second kernel-pair projection commutes with the restriction. -/
theorem map_snd : KernelPair.map f f' iX iY h ≫ pullback.snd f f = pullback.snd f' f' ≫ iX :=
  pullback.lift_snd _ _ _

/-- The kernel-pair image is the intersection of the inverse images of the covering open. -/
theorem opensRange_map :
    (KernelPair.map f f' iX iY h).opensRange =
      pullback.fst f f ⁻¹ᵁ iX.opensRange ⊓ pullback.snd f f ⁻¹ᵁ iX.opensRange := by
  apply TopologicalSpace.Opens.ext
  exact Scheme.Pullback.range_map f' f' f f iX iX iY h.symm h.symm

variable (hpre : f ⁻¹ᵁ iY.opensRange ≤ iX.opensRange)

include h hpre in
/-- A commuting open square with the full inverse image has precisely that source open. -/
theorem sourceRange_eq : f ⁻¹ᵁ iY.opensRange = iX.opensRange := by
  apply le_antisymm hpre
  simpa using SquareSections.image_preimage_le f f' iX iY h ⊤

include hpre in
/-- The induced kernel-pair open contains the full inverse image under its second projection. -/
theorem second_preimage_le :
    pullback.snd f f ⁻¹ᵁ iX.opensRange ≤ (KernelPair.map f f' iX iY h).opensRange := by
  rw [opensRange_map]
  apply le_inf ?_ le_rfl
  rw [← sourceRange_eq f f' iX iY h hpre,
    ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.KernelPair
