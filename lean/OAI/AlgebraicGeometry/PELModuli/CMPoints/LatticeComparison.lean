import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarQuotientMk

/-! # Lattice Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeComparison

noncomputable section

/-! Full stable lattices in E^3 admit explicit integral comparison maps
with O_E^3. Their composites are multiplication by one nonzero integer.
This retains the O_E action in every quotient away from that integer. -/

open scoped Classical

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)

def stableIntegerLattice : Submodule (NumberField.RingOfIntegers E) (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) where
  carrier := Λ
  zero_mem' := Λ.zero_mem
  add_mem' := Λ.add_mem
  smul_mem' a x hx := hΛ.2.2 a x hx

def integerCoordinates : (Fin 3 → NumberField.RingOfIntegers E) →ₗ[NumberField.RingOfIntegers E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E where
  toFun x i := (x i : E)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hΛ in
omit [NumberField E] in
theorem common_standard_lattice_multiple :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x : Fin 3 → NumberField.RingOfIntegers E,
      n • integerCoordinates x ∈ Λ := by
  obtain ⟨n, hn, hmem⟩ := AbelianModuli.ReferenceFamily.LatticeDenominators.common_integer_multiple_mem Λ hΛ.2.1
    (fun i : Fin 3 => Pi.single i (1 : E))
  refine ⟨n, hn, fun x => ?_⟩
  have he : n • integerCoordinates x =
      ∑ i : Fin 3, (x i : E) • (n • Pi.single i (1 : E)) := by
    have hx : integerCoordinates x = ∑ i : Fin 3, (x i : E) • Pi.single i (1 : E) := by
      ext j
      change (x j : E) = _
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [hx, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => smul_comm n (x i : E) _)
  rw [he]
  exact Λ.sum_mem (fun i _ => hΛ.2.2 (x i) _ (hmem i))

/-- Explicit integral maps in both directions between a full stable
lattice and the standard rank-three integral module. -/
theorem exists_integral_lattice_comparison :
    ∃ (c : ℤ), c ≠ 0 ∧
      ∃ (f : (Fin 3 → NumberField.RingOfIntegers E) →ₗ[NumberField.RingOfIntegers E]
            stableIntegerLattice Λ hΛ)
        (g : stableIntegerLattice Λ hΛ →ₗ[NumberField.RingOfIntegers E]
            (Fin 3 → NumberField.RingOfIntegers E)),
        (∀ x, g (f x) = c • x) ∧ (∀ x, f (g x) = c • x) := by
  obtain ⟨n, hn, hmem⟩ := common_standard_lattice_multiple Λ hΛ
  obtain ⟨m, hm, hint⟩ := AbelianModuli.ReferenceFamily.LatticeDenominators.common_integral_coordinate_multiple Λ hΛ.1
  let f : (Fin 3 → NumberField.RingOfIntegers E) →ₗ[NumberField.RingOfIntegers E]
      stableIntegerLattice Λ hΛ :=
    (n • (integerCoordinates (E := E))).codRestrict _ hmem
  let g : stableIntegerLattice Λ hΛ →ₗ[NumberField.RingOfIntegers E]
      (Fin 3 → NumberField.RingOfIntegers E) :=
    { toFun := fun x i => ⟨m • x.val i, hint x.val x.property i⟩
      map_add' := fun x y => by
        ext i
        exact smul_add m (x.val i) (y.val i)
      map_smul' := fun a x => by
        ext i
        exact smul_comm m (a : E) (x.val i) }
  refine ⟨m * n, mul_ne_zero hm hn, f, g, ?_, ?_⟩
  · intro x
    ext i
    exact (mul_smul m n (x i : E)).symm
  · intro x
    apply Subtype.ext
    ext i
    change n • (m • x.val i) = (m * n) • x.val i
    rw [smul_comm n m, ← mul_smul]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeComparison
