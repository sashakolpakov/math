import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarQuotientMk

/-! # Coordinate Lattice -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateLattice

noncomputable section

/-! Full stable lattices in arbitrary finite rank admit explicit integral comparison maps
with the standard integral module. Their composites are multiplication by one nonzero integer.
This retains the O_E action in every quotient away from that integer. -/

open scoped Classical

/-- All coordinates of a finitely generated lattice have one common
nonzero denominator in the ring of integers of the number field. -/
theorem common_coordinate_integral_multiple {E : Type*} [Field E] [NumberField E]
    {r : ℕ} (Λ : Submodule ℤ (Fin r → E)) (hΛ : Λ.FG) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ Λ, ∀ i, IsIntegral ℤ (n • x i) := by
  obtain ⟨s, hs⟩ := hΛ
  let t : Finset E := s.biUnion (fun x => Finset.univ.image x)
  let : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  let : Algebra.IsAlgebraic ℤ E := Algebra.IsAlgebraic.trans ℤ ℚ E
  obtain ⟨n, hn, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ t
  refine ⟨n, hn, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span ℤ (s : Set (Fin r → E)) := hs.symm ▸ hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
      intro i
      exact hint (x i) (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
  | zero =>
      intro i
      simpa only [Pi.zero_apply, smul_zero] using (isIntegral_zero : IsIntegral ℤ (0 : E))
  | add x y _ _ hx hy =>
      intro i
      simpa only [Pi.add_apply, smul_add] using (hx i).add (hy i)
  | smul a x _ hx =>
      intro i
      simpa only [Pi.smul_apply, smul_comm n a] using (hx i).smul a

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  {r : ℕ}

def FullStableCoordinateLattice (Λ : Submodule ℤ (Fin r → E)) : Prop :=
  Λ.FG ∧ Submodule.span ℚ (Λ : Set (Fin r → E)) = ⊤ ∧
    ∀ (a : NumberField.RingOfIntegers E) (x : Fin r → E), x ∈ Λ → (a : E) • x ∈ Λ

variable (Λ : Submodule ℤ (Fin r → E)) (hΛ : FullStableCoordinateLattice Λ)

def stableCoordinateLattice : Submodule (NumberField.RingOfIntegers E) ((Fin r → E)) where
  carrier := Λ
  zero_mem' := Λ.zero_mem
  add_mem' := Λ.add_mem
  smul_mem' a x hx := hΛ.2.2 a x hx

def integralCoordinateMap : (Fin r → NumberField.RingOfIntegers E) →ₗ[NumberField.RingOfIntegers E] (Fin r → E) where
  toFun x i := (x i : E)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hΛ in
omit [NumberField E] in
theorem common_coordinate_lattice_multiple :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x : Fin r → NumberField.RingOfIntegers E,
      n • integralCoordinateMap x ∈ Λ := by
  obtain ⟨n, hn, hmem⟩ := AbelianModuli.ReferenceFamily.LatticeDenominators.common_integer_multiple_mem Λ hΛ.2.1
    (fun i : Fin r => Pi.single i (1 : E))
  refine ⟨n, hn, fun x => ?_⟩
  have he : n • integralCoordinateMap x =
      ∑ i : Fin r, (x i : E) • (n • Pi.single i (1 : E)) := by
    have hx : integralCoordinateMap x = ∑ i : Fin r, (x i : E) • Pi.single i (1 : E) := by
      ext j
      change (x j : E) = _
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [hx, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => smul_comm n (x i : E) _)
  rw [he]
  exact Λ.sum_mem (fun i _ => hΛ.2.2 (x i) _ (hmem i))

/-- Explicit integral maps in both directions between a full stable
lattice and the standard integral module. -/
theorem exists_coordinate_lattice_comparison :
    ∃ (c : ℤ), c ≠ 0 ∧
      ∃ (f : (Fin r → NumberField.RingOfIntegers E) →ₗ[NumberField.RingOfIntegers E]
            stableCoordinateLattice Λ hΛ)
        (g : stableCoordinateLattice Λ hΛ →ₗ[NumberField.RingOfIntegers E]
            (Fin r → NumberField.RingOfIntegers E)),
        (∀ x, g (f x) = c • x) ∧ (∀ x, f (g x) = c • x) := by
  obtain ⟨n, hn, hmem⟩ := common_coordinate_lattice_multiple Λ hΛ
  obtain ⟨m, hm, hint⟩ := common_coordinate_integral_multiple Λ hΛ.1
  let f : (Fin r → NumberField.RingOfIntegers E) →ₗ[NumberField.RingOfIntegers E]
      stableCoordinateLattice Λ hΛ :=
    (n • (integralCoordinateMap (E := E))).codRestrict _ hmem
  let g : stableCoordinateLattice Λ hΛ →ₗ[NumberField.RingOfIntegers E]
      (Fin r → NumberField.RingOfIntegers E) :=
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

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateLattice
