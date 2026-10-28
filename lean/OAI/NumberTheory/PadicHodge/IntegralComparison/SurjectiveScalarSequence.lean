import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Surjective Scalar Sequence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarSequence

noncomputable section

/-! A quotient with the kernel of scalar multiplication identifies with its image. -/

open _root_.CategoryTheory

universe u v w z

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  (q : M →ₗ[R] N) (hq : Function.Surjective q) (r : R)
  (hk : ∀ x : M, q x = 0 ↔ r • x = 0)

def inclusion : N →ₗ[R] M :=
  ((LinearMap.ker q).liftQ (DistribSMul.toLinearMap R M r)
    (fun x hx => (hk x).mp hx)).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap

theorem inclusion_apply (x : M) : inclusion q hq r hk (q x) = r • x := by
  change (LinearMap.ker q).liftQ (DistribSMul.toLinearMap R M r)
    (fun y hy => (hk y).mp hy) ((q.quotKerEquivOfSurjective hq).symm (q x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

theorem injective : Function.Injective (inclusion q hq r hk) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro y hy
  obtain ⟨x, rfl⟩ := hq y
  change q x = 0
  exact (hk x).mpr ((inclusion_apply q hq r hk x).symm.trans hy)

variable {P : Type z} [AddCommGroup P] [Module R P] (g : M →ₗ[R] P)
  (hg : ∀ x : M, g x = 0 ↔ ∃ y : M, r • y = x)

include hg in
theorem exact : Function.Exact (inclusion q hq r hk) g := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hg x).mp hx
    exact ⟨q y, (inclusion_apply q hq r hk y).trans hy⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hq y
    exact (hg _).mpr ⟨z, (inclusion_apply q hq r hk z).symm⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarSequence
