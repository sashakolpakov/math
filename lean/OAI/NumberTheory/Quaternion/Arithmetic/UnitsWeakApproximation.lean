import OAI.NumberTheory.Quaternion.Arithmetic.FiniteScalarDensity
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Units Weak Approximation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.UnitsWeakApproximation

noncomputable section

/-! Weak approximation passes from a finite-dimensional algebra to
its unit group. Invertibility is reflected by any faithful ring map,
using finite-dimensional linear algebra. -/

open scoped Classical
open Set

variable {F A B : Type*} [Field F] [Ring A] [Algebra F A] [FiniteDimensional F A] [Ring B]

include F in
theorem finiteDimensional_isUnit_of_injective_map (f : A →+* B) (hf : Function.Injective f)
    {a : A} (ha : IsUnit (f a)) : IsUnit a := by
  have hi : Function.Injective (Algebra.lmul F A a) := by
    intro x y hxy
    apply hf
    apply ha.mul_left_cancel
    change a * x = a * y at hxy
    simpa only [← map_mul] using congrArg f hxy
  apply (Algebra.lmul_isUnit_iff (R := F)).mp
  apply (Module.End.isUnit_iff _).mpr
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

variable {ι : Type*} [Finite ι] {C : ι → Type*} [∀ i, Ring (C i)]
  [∀ i, TopologicalSpace (C i)] [∀ i, IsOpenUnits (C i)]

def unitsPiDiagonal (f : ∀ i, A →+* C i) : Aˣ →* (∀ i, (C i)ˣ) :=
  MonoidHom.pi (fun i => Units.map (f i))

omit [Algebra F A] [FiniteDimensional F A] in
theorem finite_units_pi_val_isOpenMap :
    IsOpenMap (fun x : ∀ i, (C i)ˣ => fun i => (x i).val) := by
  exact IsOpenMap.piMap (fun i => (IsOpenUnits.isOpenEmbedding_unitsVal (M := C i)).isOpenMap)
    (by simp)

include F in
theorem denseRange_unitsPiDiagonal (f : ∀ i, A →+* C i)
    (hf : ∀ i, Function.Injective (f i))
    (hd : DenseRange (fun a : A => fun i => f i a)) : DenseRange (unitsPiDiagonal f) := by
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    let := hi
    intro x
    have he : unitsPiDiagonal f 1 = x := Subsingleton.elim _ _
    exact subset_closure ⟨1, he⟩
  | inr hi =>
    let := hi
    let i₀ : ι := Classical.choice hi
    intro x
    rw [mem_closure_iff]
    intro V hV hx
    have ho := finite_units_pi_val_isOpenMap (C := C) V hV
    obtain ⟨a, y, hy, hya⟩ := hd.exists_mem_open ho ⟨(fun i => (x i).val), x, hx, rfl⟩
    have ha : IsUnit a := finiteDimensional_isUnit_of_injective_map (F := F) (f i₀) (hf i₀) (by
      rw [← congrFun hya i₀]
      exact (y i₀).isUnit)
    obtain ⟨a, rfl⟩ := ha
    have he : unitsPiDiagonal f a = y := by
      funext i
      apply Units.ext
      exact (congrFun hya i).symm
    exact ⟨unitsPiDiagonal f a, he ▸ hy, Set.mem_range_self a⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.UnitsWeakApproximation
