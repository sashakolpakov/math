import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups
import Mathlib.RingTheory.Algebraic.Integral

/-! # Lattice Denominators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators

noncomputable section

/-! Clear denominators against the actual integral lattice. These
lemmas make sufficiently deep congruences comparable to integral
matrix congruences without assuming a preferred lattice basis. -/

open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem integer_multiple_mem_of_span (Λ : Submodule ℤ V) (x : V)
    (hx : x ∈ Submodule.span ℚ (Λ : Set V)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, (one_smul ℤ x).symm ▸ hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨n, hn, hx⟩ := hx
      obtain ⟨m, hm, hy⟩ := hy
      refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
      rw [smul_add]
      exact Λ.add_mem
        (by simpa only [mul_smul, smul_comm n m x] using Λ.smul_mem m hx)
        (by simpa only [mul_smul] using Λ.smul_mem n hy)
  | smul a x _ hx =>
      obtain ⟨n, hn, hx⟩ := hx
      refine ⟨n * (a.den : ℤ), mul_ne_zero hn (by exact_mod_cast a.den_nz), ?_⟩
      have hscalar : (((n * (a.den : ℤ) : ℤ) : ℚ) * a) = (a.num : ℚ) * (n : ℚ) := by
        rw [Int.cast_mul, Int.cast_natCast, mul_assoc, Rat.den_mul_eq_num]
        exact mul_comm _ _
      have he : (n * (a.den : ℤ)) • (a • x) = a.num • (n • x) := by
        calc
          _ = ((((n * (a.den : ℤ) : ℤ) : ℚ) * a)) • x := by
            exact (Int.cast_smul_eq_zsmul ℚ (n * (a.den : ℤ)) (a • x)).symm.trans
              (mul_smul _ _ _).symm
          _ = ((a.num : ℚ) * (n : ℚ)) • x := congrArg (fun c : ℚ => c • x) hscalar
          _ = _ := by rw [mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      rw [he]
      exact Λ.smul_mem a.num hx

/-- Finitely many vectors have one common nonzero lattice denominator. -/
theorem common_integer_multiple_mem (Λ : Submodule ℤ V)
    (hΛ : Submodule.span ℚ (Λ : Set V) = ⊤)
    {I : Type*} [Fintype I] (v : I → V) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ i, n • v i ∈ Λ := by
  choose n hn hv using fun i => integer_multiple_mem_of_span Λ (v i)
    (hΛ.symm ▸ (Submodule.mem_top : v i ∈ (⊤ : Submodule ℚ V)))
  refine ⟨∏ i, n i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn i), ?_⟩
  intro i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, mul_smul, smul_comm]
  exact Λ.smul_mem c (hv i)

/-- All coordinates of a finitely generated lattice have one common
nonzero denominator in the ring of integers of the number field. -/
theorem common_integral_coordinate_multiple {E : Type*} [Field E] [NumberField E]
    (Λ : Submodule ℤ (Fin 3 → E)) (hΛ : Λ.FG) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ Λ, ∀ i, IsIntegral ℤ (n • x i) := by
  obtain ⟨s, hs⟩ := hΛ
  let t : Finset E := s.biUnion (fun x => Finset.univ.image x)
  let : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  let : Algebra.IsAlgebraic ℤ E := Algebra.IsAlgebraic.trans ℤ ℚ E
  obtain ⟨n, hn, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ t
  refine ⟨n, hn, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span ℤ (s : Set (Fin 3 → E)) := hs.symm ▸ hx
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

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators
