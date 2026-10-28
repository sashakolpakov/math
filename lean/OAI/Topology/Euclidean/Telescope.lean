import Mathlib.LinearAlgebra.Pi

/-! # Telescope -/

namespace OAI.Topology.Euclidean.Telescope

noncomputable section

/-!
# The difference map of a countable inverse system of modules

For transition maps `t i: V (i + 1) →ₗ[R] V i`, the difference map on the
product sends `x` to `fun i => x i - t i (x (i + 1))`. Its kernel is exactly
the submodule of compatible sequences. If every transition is surjective,
successively choosing preimages constructs a preimage of any product element.

This module proves only these algebraic facts. In applications, surjectivity
of geometric restriction maps or of the resulting difference map must be
established separately.
-/

universe u v w

variable (R : Type v) [Ring R] (V : ℕ → Type u)
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  (t : ∀ i, V (i + 1) →ₗ[R] V i)

/-- The compatible sequences of the specified inverse system. -/
def telescopeCompatible : Submodule R (∀ i, V i) where
  carrier := {x | ∀ i, x i = t i (x (i + 1))}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro x y hx hy i
    simp only [Pi.add_apply, map_add, hx i, hy i]
  smul_mem' := by
    intro r x hx i
    simp only [Pi.smul_apply, map_smul, hx i]

@[simp]
theorem mem_telescopeCompatible (x : ∀ i, V i) :
    x ∈ telescopeCompatible R V t ↔ ∀ i, x i = t i (x (i + 1)) := Iff.rfl

/-- The telescope difference map on the countable product. -/
def telescopeDelta : (∀ i, V i) →ₗ[R] (∀ i, V i) :=
  LinearMap.pi fun i => LinearMap.proj i - (t i).comp (LinearMap.proj (i + 1))

@[simp]
theorem telescopeDelta_apply (x : ∀ i, V i) (i : ℕ) :
    telescopeDelta R V t x i = x i - t i (x (i + 1)) := rfl

/-- Vanishing of the difference map is precisely adjacent compatibility. -/
theorem telescopeDelta_eq_zero_iff (x : ∀ i, V i) :
    telescopeDelta R V t x = 0 ↔ ∀ i, x i = t i (x (i + 1)) := by
  simp only [funext_iff, telescopeDelta_apply, Pi.zero_apply, sub_eq_zero]

/-- The kernel is the actual submodule of compatible sequences. -/
theorem ker_telescopeDelta :
    LinearMap.ker (telescopeDelta R V t) = telescopeCompatible R V t := by
  ext x
  exact telescopeDelta_eq_zero_iff R V t x

/-- A chosen preimage of a product element, constructed recursively from the
surjectivity of each transition. The initial component is chosen to be zero;
no linearity of this choice of preimages is asserted. -/
def telescopePreimage (ht : ∀ i, Function.Surjective (t i))
    (y : ∀ i, V i) : ∀ i, V i :=
  Nat.rec (motive := V) 0 fun i x => Function.surjInv (ht i) (x - y i)

@[simp]
theorem telescopePreimage_zero (ht : ∀ i, Function.Surjective (t i))
    (y : ∀ i, V i) : telescopePreimage R V t ht y 0 = 0 := rfl

@[simp]
theorem telescopePreimage_succ (ht : ∀ i, Function.Surjective (t i))
    (y : ∀ i, V i) (i : ℕ) :
    telescopePreimage R V t ht y (i + 1) =
      Function.surjInv (ht i) (telescopePreimage R V t ht y i - y i) := rfl

/-- The recursively constructed sequence is a genuine preimage under Δ. -/
theorem telescopeDelta_preimage (ht : ∀ i, Function.Surjective (t i))
    (y : ∀ i, V i) :
    telescopeDelta R V t (telescopePreimage R V t ht y) = y := by
  funext i
  rw [telescopeDelta_apply, telescopePreimage_succ, Function.surjInv_eq (ht i)]
  exact sub_sub_cancel _ _

/-- Surjective transition maps imply surjectivity of the telescope difference
map, by the explicit recursive construction above. -/
theorem telescopeDelta_surjective (ht : ∀ i, Function.Surjective (t i)) :
    Function.Surjective (telescopeDelta R V t) := by
  intro y
  exact ⟨telescopePreimage R V t ht y, telescopeDelta_preimage R V t ht y⟩

variable (W : ℕ → Type w) [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
  (s : ∀ i, W (i + 1) →ₗ[R] W i)
  (f : ∀ i, V i →ₗ[R] W i)
  (hf : ∀ i, (f i).comp (t i) = (s i).comp (f (i + 1)))

include hf

/-- A commuting family of maps between inverse systems commutes with Δ on
their products. -/
theorem telescopeDelta_naturality :
    (telescopeDelta R W s).comp (LinearMap.piMap f) =
      (LinearMap.piMap f).comp (telescopeDelta R V t) := by
  ext x i
  change f i (x i) - s i (f (i + 1) (x (i + 1))) =
    f i (x i - t i (x (i + 1)))
  rw [map_sub]
  have hi := DFunLike.congr_fun (hf i) (x (i + 1))
  change f i (t i (x (i + 1))) = s i (f (i + 1) (x (i + 1))) at hi
  rw [hi]

/-- The product map of a morphism of inverse systems carries compatible
sequences to compatible sequences. -/
theorem telescopeCompatible_map_mem (x : ∀ i, V i)
    (hx : x ∈ telescopeCompatible R V t) :
    LinearMap.piMap f x ∈ telescopeCompatible R W s := by
  intro i
  change f i (x i) = s i (f (i + 1) (x (i + 1)))
  rw [hx i]
  exact DFunLike.congr_fun (hf i) (x (i + 1))

end

end OAI.Topology.Euclidean.Telescope
