import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.StandardLattice
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Lattice.CM

noncomputable section

/-! At primes avoiding the two constructed lattice denominators, every
integral local embedding identifies the reference lattice with Z_q³. -/

open scoped Classical
open _root_.NumberField

variable {E : Type*} [Field E] [NumberField E] {q : ℕ} [Fact q.Prime]

def localImage (τ : E →+* ℚ_[q]) : (Fin 3 → E) →ₗ[ℤ] (Fin 3 → ℚ_[q]) where
  toFun x i := τ (x i)
  map_add' x y := by ext i; exact map_add τ _ _
  map_smul' n x := by ext i; exact map_zsmul τ n (x i)

def localLattice (τ : E →+* ℚ_[q]) (Λ : Submodule ℤ (Fin 3 → E)) :
    Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  Submodule.span ℤ_[q] (localImage τ '' (Λ : Set (Fin 3 → E)))

def standard : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  Submodule.span ℤ_[q] (Set.range fun i : Fin 3 => Pi.single i 1)

theorem natCast_isUnit (n : ℕ) (hn : Nat.Coprime q n) : IsUnit (n : ℤ_[q]) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h
  rw [← PadicInt.ker_toZMod] at h
  have hz : (n : ZMod q) = 0 := by
    simpa only [RingHom.mem_ker, map_natCast] using h
  exact ((ZMod.isUnit_iff_coprime n q).mpr hn.symm).ne_zero hz

theorem localImage_single (τ : E →+* ℚ_[q]) (i : Fin 3) (x : E) :
    localImage τ (Pi.single i x) = Pi.single i (τ x) := by
  ext j
  by_cases h : i = j
  · subst j; simp [localImage]
  · simp [localImage, Pi.single_eq_of_ne (Ne.symm h)]

theorem localImage_nsmul (τ : E →+* ℚ_[q]) (n : ℕ) (x : Fin 3 → E) :
    localImage τ (n • x) = (n : ℤ_[q]) • localImage τ x := by
  rw [map_nsmul, Nat.cast_smul_eq_nsmul]

omit [NumberField E] in
theorem integral_vector_mem (v : Fin 3 → ℤ_[q]) :
    (fun i => (v i : ℚ_[q])) ∈ standard (q := q) := by
  have hsingle (i : Fin 3) :
      Pi.single i (v i : ℚ_[q]) ∈ standard (q := q) := by
    have h := (standard (q := q)).smul_mem (v i)
      (Submodule.subset_span ⟨i, rfl⟩)
    convert h using 1
    ext j
    by_cases hij : i = j
    · subst j
      simp only [Pi.smul_apply, Pi.single_eq_same]
      change (v i : ℚ_[q]) = (v i : ℚ_[q]) * 1
      exact (mul_one _).symm
    · simp [Pi.single_eq_of_ne (Ne.symm hij)]
  rw [← Finset.univ_sum_single (fun i => (v i : ℚ_[q]))]
  exact Submodule.sum_mem _ (fun i _ => hsingle i)

theorem standard_image_mem (τ : E →+* ℚ_[q])
    (χ : RingOfIntegers E →+* ℤ_[q])
    (hχ : ∀ a : RingOfIntegers E, τ a = (χ a : ℚ_[q]))
    (x : Fin 3 → E) (hx : x ∈ StandardLattice.CM.standardLattice E) :
    localImage τ x ∈ standard (q := q) := by
  obtain ⟨y, rfl⟩ := hx
  convert integral_vector_mem (fun i => χ (y i)) using 1
  ext i
  exact hχ (y i)

/-- The two integral inclusions alone imply the standard local frame when
their multipliers are units. No local-frame hypothesis is used. -/
theorem localLattice_eq_standard (τ : E →+* ℚ_[q])
    (χ : RingOfIntegers E →+* ℤ_[q])
    (hχ : ∀ a : RingOfIntegers E, τ a = (χ a : ℚ_[q]))
    (Λ : Submodule ℤ (Fin 3 → E)) (m n : ℕ)
    (hm : Nat.Coprime q m) (hn : Nat.Coprime q n)
    (hml : ∀ x ∈ StandardLattice.CM.standardLattice E, m • x ∈ Λ)
    (hnl : ∀ x ∈ Λ, n • x ∈ StandardLattice.CM.standardLattice E) :
    localLattice τ Λ = standard (q := q) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    apply ((standard (q := q)).smul_mem_iff_of_isUnit (natCast_isUnit n hn)).mp
    rw [← localImage_nsmul]
    exact standard_image_mem τ χ hχ _ (hnl x hx)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply ((localLattice τ Λ).smul_mem_iff_of_isUnit (natCast_isUnit m hm)).mp
    have h := Submodule.subset_span (R := ℤ_[q])
      (s := localImage τ '' (Λ : Set (Fin 3 → E)))
      ⟨m • Pi.single i (1 : E),
        hml _ (StandardLattice.CM.single_integer_mem E i 1), rfl⟩
    change localImage τ (m • Pi.single i 1) ∈ localLattice τ Λ at h
    rw [localImage_nsmul, localImage_single, map_one] at h
    exact h

/-- A single positive bound works simultaneously for every integral local
embedding of the number field. -/
theorem exists_uniform_local_frame (Λ : Submodule ℤ (Fin 3 → E))
    (hfg : Λ.FG) (hfull : Submodule.span ℚ (Λ : Set (Fin 3 → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime p d →
      ∀ (τ : E →+* ℚ_[p]) (χ : RingOfIntegers E →+* ℤ_[p]),
      (∀ a : RingOfIntegers E, τ a = (χ a : ℚ_[p])) →
      localLattice τ Λ = standard (q := p) := by
  obtain ⟨m, n, hm, hn, hml, hnl⟩ :=
    StandardLattice.CM.integer_bounds E Λ hfg hfull
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  intro p _ hp τ χ hχ
  exact localLattice_eq_standard τ χ hχ Λ m n
    (Nat.coprime_mul_iff_right.mp hp).1 (Nat.coprime_mul_iff_right.mp hp).2 hml hnl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Lattice.CM
