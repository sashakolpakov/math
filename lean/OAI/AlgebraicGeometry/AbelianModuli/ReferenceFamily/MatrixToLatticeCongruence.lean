import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! # Matrix To Lattice Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixToLatticeCongruence

noncomputable section

/-! Transfer literal integral matrix congruences to the specified
integral lattice using its fixed coordinate and basis denominators.
The lattice is only required to have its actual integral scalar action.
-/

variable {E I : Type*} [Field E] [NumberField E] [Fintype I] [DecidableEq I]

omit [NumberField E] in
theorem integral_vector_multiple_mem_lattice
    (Λ : Submodule ℤ (I → E))
    (hO : ∀ a : NumberField.RingOfIntegers E, ∀ x ∈ Λ, (a : E) • x ∈ Λ)
    (d : ℤ) (hbasis : ∀ j : I, d • (Pi.single j (1 : E)) ∈ Λ)
    (z : I → E) (hz : ∀ i, IsIntegral ℤ (z i)) : d • z ∈ Λ := by
  have he : d • z = ∑ j, z j • (d • (Pi.single j (1 : E))) := by
    ext i
    simp [Pi.single_apply, zsmul_eq_mul, mul_comm]
  rw [he]
  apply Λ.sum_mem
  intro j _
  exact hO ⟨z j, hz j⟩ (d • Pi.single j 1) (hbasis j)

omit [NumberField E] in
theorem integral_matrix_congruence_on_lattice
    (Λ : Submodule ℤ (I → E))
    (hO : ∀ a : NumberField.RingOfIntegers E, ∀ x ∈ Λ, (a : E) • x ∈ Λ)
    (d c : ℤ) (hbasis : ∀ j : I, d • (Pi.single j (1 : E)) ∈ Λ)
    (hcoords : ∀ x ∈ Λ, ∀ i, IsIntegral ℤ (c • x i))
    (D ℓ N : ℕ) (k : ℤ) (hlevel : (ℓ : ℤ) = (N : ℤ) * d * c * k)
    (f : (I → E) →ₗ[E] (I → E))
    (A : Matrix I I (NumberField.RingOfIntegers E))
    (hA : ∀ i j, (D : E) * (LinearMap.toMatrix' f i j - (1 : Matrix I I E) i j) =
      (ℓ : E) * (A i j : E)) :
    ∀ x ∈ Λ, ∃ y ∈ Λ, (D : E) • (f x - x) = (N : E) • y := by
  intro x hx
  let A₀ := A.map (algebraMap (NumberField.RingOfIntegers E) E)
  let C := A₀.mulVec (c • x)
  have hC : ∀ i, IsIntegral ℤ (C i) := by
    intro i
    change (∑ j, (A i j : E) * (c • x j)) ∈ integralClosure ℤ E
    apply (integralClosure ℤ E).sum_mem
    intro j _
    exact (integralClosure ℤ E).mul_mem (A i j).property (hcoords x hx j)
  have hy : d • (k • C) ∈ Λ :=
    integral_vector_multiple_mem_lattice Λ hO d hbasis (k • C)
      (fun i => (hC i).smul k)
  have hmat : (D : E) • (LinearMap.toMatrix' f - 1) = (ℓ : E) • A₀ := by
    ext i j
    exact hA i j
  have he := congrArg (fun M : Matrix I I E => M.mulVec x) hmat
  simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, LinearMap.toMatrix'_mulVec,
    Matrix.one_mulVec] at he
  have hlevelE : (ℓ : E) = (N : E) * (d : E) * (c : E) * (k : E) := by
    simpa only [Int.cast_natCast, Int.cast_mul] using congrArg (fun n : ℤ => (n : E)) hlevel
  have hright : (N : E) • (d • (k • C)) = (ℓ : E) • A₀.mulVec x := by
    dsimp only [C]
    rw [← Int.cast_smul_eq_zsmul E d, ← Int.cast_smul_eq_zsmul E k,
      ← Int.cast_smul_eq_zsmul E c, Matrix.mulVec_smul]
    simp only [smul_smul]
    rw [hlevelE]
    congr 1
    ring
  exact ⟨d • (k • C), hy, he.trans hright.symm⟩

theorem integer_multiple_congruent_one_on_lattice
    {V : Type*} [AddCommGroup V] [Module ℤ V]
    (Λ : Submodule ℤ V) (D N : ℕ) (hD : (N : ℤ) ∣ (D : ℤ) - 1)
    (f : V → V)
    (hf : ∀ x ∈ Λ, ∃ y ∈ Λ, D • (f x - x) = N • y) :
    ∀ x ∈ Λ, ∃ y ∈ Λ, D • f x - x = N • y := by
  obtain ⟨k, hk⟩ := hD
  intro x hx
  obtain ⟨y, hy, he⟩ := hf x hx
  have hscalar : D • x - x = N • (k • x) := by
    calc
      D • x - x = ((D : ℤ) - 1) • x := by
        rw [sub_zsmul, one_zsmul, natCast_zsmul, sub_eq_add_neg]
      _ = ((N : ℤ) * k) • x := congrArg (fun a : ℤ => a • x) hk
      _ = N • (k • x) := by rw [mul_zsmul, natCast_zsmul]
  refine ⟨y + k • x, Λ.add_mem hy (Λ.toAddSubgroup.zsmul_mem hx k), ?_⟩
  calc
    D • f x - x = D • (f x - x) + (D • x - x) := by rw [nsmul_sub]; abel
    _ = N • y + N • (k • x) := by rw [he, hscalar]
    _ = N • (y + k • x) := by rw [nsmul_add]

theorem integer_multiple_mem_lattice_of_congruence
    {V : Type*} [AddCommGroup V] [Module ℤ V]
    (Λ : Submodule ℤ V) (D N : ℕ) (f : V → V)
    (hf : ∀ x ∈ Λ, ∃ y ∈ Λ, D • f x - x = N • y) :
    ∀ x ∈ Λ, D • f x ∈ Λ := by
  intro x hx
  obtain ⟨y, hy, he⟩ := hf x hx
  have hNy : N • y ∈ Λ := Λ.toAddSubgroup.nsmul_mem hy N
  have hm := Λ.add_mem hNy hx
  rwa [← he, sub_add_cancel] at hm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixToLatticeCongruence
