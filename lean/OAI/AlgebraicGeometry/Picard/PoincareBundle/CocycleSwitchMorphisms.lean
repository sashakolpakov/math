import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleNormalization

/-! # Cocycle Switch Morphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchMorphisms

noncomputable section

/-!
# Morphisms of extracted coactions preserve the entire original descent switch
-/

open TensorProduct
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSwitch OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchNext OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleNormalization

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {M N : Type u} [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module R M] [IsScalarTower R S M]
  [Module S N] [Module R N] [IsScalarTower R S N]

/-- The base-ring tensor extension of an S-linear morphism. -/
def tensorMap (a : M →ₗ[S] N) : S ⊗[R] M →ₗ[R] S ⊗[R] N :=
  TensorProduct.map (LinearMap.id : S →ₗ[R] S) (a.restrictScalars R)

theorem tensorMap_tmul (a : M →ₗ[S] N) (s : S) (m : M) :
    tensorMap (R := R) a (s ⊗ₜ[R] m) = s ⊗ₜ[R] a m := rfl

/-- Tensor extension respects scalar multiplication in the module factor. -/
theorem tensorMap_secondScalar (a : M →ₗ[S] N) (s : S) (z : S ⊗[R] M) :
    tensorMap (R := R) a (DescentSwitch.secondScalar (R := R) (M := M) s z) =
      DescentSwitch.secondScalar (R := R) (M := N) s (tensorMap (R := R) a z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t m =>
      change t ⊗ₜ[R] a (s • m) = t ⊗ₜ[R] (s • a m)
      rw [a.map_smul]

/-- A coaction-compatible morphism respects the entire normalized descent switch. -/
theorem switch_compatible (D : CocycleSwitchNext.CocycleSwitch R S M) (E : CocycleSwitchNext.CocycleSwitch R S N)
    (a : M →ₗ[S] N)
    (h : ∀ m, tensorMap (R := R) a (D.coaction m) = E.coaction (a m))
    (z : S ⊗[R] M) :
    tensorMap (R := R) a (D.switch z) = E.switch (tensorMap (R := R) a z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
      rw [CocycleNormalization.switch_tmul D, tensorMap_secondScalar, h m, tensorMap_tmul]
      exact (CocycleNormalization.switch_tmul E s (a m)).symm

/-- Conversely, compatibility with the original switch preserves its extracted coaction. -/
theorem coaction_compatible (D : CocycleSwitchNext.CocycleSwitch R S M) (E : CocycleSwitchNext.CocycleSwitch R S N)
    (a : M →ₗ[S] N)
    (h : ∀ z, tensorMap (R := R) a (D.switch z) = E.switch (tensorMap (R := R) a z))
    (m : M) : tensorMap (R := R) a (D.coaction m) = E.coaction (a m) :=
  h (1 ⊗ₜ[R] m)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchMorphisms
