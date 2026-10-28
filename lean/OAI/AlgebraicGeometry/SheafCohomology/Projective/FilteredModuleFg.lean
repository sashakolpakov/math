import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialFilteredAlgebra
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Filtered Module Fg -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredModuleFg.Dimension

noncomputable section

section

/-! Degree filtrations are controlled by products of finite-dimensional subspaces. -/

open _root_.MvPolynomial
open scoped TensorProduct

variable {K B σ : Type*} [Field K] [CommRing B] [Algebra K B]

theorem submodule_pow_monotone (W : Submodule K B) (hW : 1 ≤ W) :
    Monotone (fun n : ℕ => W ^ n) := by
  apply monotone_nat_of_le_succ
  intro n
  calc
    W ^ n = W ^ n * 1 := (mul_one _).symm
    _ ≤ W ^ n * W := Submodule.smul_mono le_rfl hW
    _ = W ^ (n + 1) := (pow_succ W n).symm

theorem aeval_monomial_mem_submodule_pow
    (v : σ → B) (W : Submodule K B) (hv : ∀ i, v i ∈ W)
    (d : σ →₀ ℕ) (a : K) :
    MvPolynomial.aeval v (MvPolynomial.monomial d a) ∈ W ^ (d.sum fun _ e => e) := by
  classical
  have hp (s : Finset σ) : (∏ i ∈ s, v i ^ d i) ∈ W ^ (∑ i ∈ s, d i) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]; exact Submodule.one_le.mp le_rfl
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow W (hv i) (d i)) ih
  rw [MvPolynomial.aeval_monomial]
  simpa only [Algebra.smul_def, Finsupp.prod] using
    (W ^ (d.sum fun _ e => e)).smul_mem a (hp d.support)

theorem polynomialFilteredPiece_le_pow
    (v : σ → B) (W : Submodule K B) (hW : 1 ≤ W) (hv : ∀ i, v i ∈ W) (n : ℕ) :
    PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n ≤ W ^ n := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := (PolynomialFilteredAlgebra.Dimension.mem_polynomialFilteredPiece v n x).mp hx
  rw [p.as_sum, map_sum]
  apply (W ^ n).sum_mem
  intro d hd
  exact submodule_pow_monotone W hW ((MvPolynomial.le_totalDegree hd).trans hp)
    (aeval_monomial_mem_submodule_pow v W hv d (p.coeff d))

theorem polynomialFilteredPiece_mul_le (v : σ → B) (n m : ℕ) :
    PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n * PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece v m ≤
      PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece v (n + m) :=
  Submodule.mul_le.mpr (fun _ hx _ hy => PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece_mul v hx hy)

theorem finite_submodule_product_finrank_le (M N : Submodule K B)
    [Module.Finite K M] [Module.Finite K N] :
    Module.finrank K (M * N) ≤ Module.finrank K M * Module.finrank K N := by
  have h := LinearMap.finrank_le_finrank_of_surjective (Submodule.mulMap'_surjective M N)
  rw [Module.finrank_tensorProduct] at h
  exact h

theorem submodule_pow_mul_le_filtered
    (w : σ → B) (W T : Submodule K B) (c : ℕ)
    (h : W * T ≤ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) w c * T) (n : ℕ) :
    W ^ n * T ≤ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) w (n * c) * T := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, zero_mul]
    have h₁ : (1 : Submodule K B) ≤ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) w 0 :=
      Submodule.one_le.mpr (by simpa using PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece_algebraMap w 0 (1 : K))
    calc
      T = (1 : Submodule K B) * T := (one_mul T).symm
      _ ≤ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w 0 * T := Submodule.smul_mono h₁ (le_refl T)
  | succ n ih =>
    calc
      W ^ (n + 1) * T = W ^ n * (W * T) := by rw [pow_succ, mul_assoc]
      _ ≤ W ^ n * (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w c * T) := Submodule.smul_mono le_rfl h
      _ = PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w c * (W ^ n * T) := by ac_rfl
      _ ≤ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w c * (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w (n * c) * T) :=
        Submodule.smul_mono le_rfl ih
      _ = (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w c * PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w (n * c)) * T :=
        (mul_assoc _ _ _).symm
      _ ≤ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w (c + n * c) * T :=
        Submodule.smul_mono (polynomialFilteredPiece_mul_le w c (n * c)) le_rfl
      _ = PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece w ((n + 1) * c) * T := by rw [Nat.add_mul, one_mul, Nat.add_comm c]

end

section

/-! Degree filtrations of finite modules and bounded shifts under module maps. -/

open _root_.MvPolynomial

variable {K B σ M N : Type*} [Field K] [CommRing B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module B M] [IsScalarTower K B M]
    [AddCommGroup N] [Module K N] [Module B N] [IsScalarTower K B N]

def polynomialFilteredModule (v : σ → B) (T : Submodule K M) (n : ℕ) : Submodule K M :=
  PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n • T

theorem polynomialFilteredModule_mono (v : σ → B) (T : Submodule K M) :
    Monotone (polynomialFilteredModule v T) :=
  fun _ _ h => Submodule.smul_mono (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece_mono v h) le_rfl

theorem polynomialFilteredModule_contains (v : σ → B) (T : Submodule K M) (n : ℕ) :
    T ≤ polynomialFilteredModule v T n := by
  have h₁ : (1 : Submodule K B) ≤ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n :=
    Submodule.one_le.mpr (by simpa using PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece_algebraMap v n (1 : K))
  exact (Submodule.one_smul T).symm.le.trans (Submodule.smul_mono h₁ le_rfl)

theorem polynomialFilteredModule_smul (v : σ → B) (T : Submodule K M)
    {n m : ℕ} {a : B} {x : M} (ha : a ∈ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n)
    (hx : x ∈ polynomialFilteredModule v T m) :
    a • x ∈ polynomialFilteredModule v T (n + m) := by
  have h : PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n • polynomialFilteredModule v T m ≤
      polynomialFilteredModule v T (n + m) := by
    unfold polynomialFilteredModule
    rw [← Submodule.smul_assoc]
    exact Submodule.smul_mono (polynomialFilteredPiece_mul_le v n m) le_rfl
  exact h (Submodule.smul_mem_smul ha hx)

theorem polynomialFilteredModule_exhaustive (v : σ → B)
    (hv : Algebra.adjoin K (Set.range v) = ⊤) (T : Submodule K M)
    (hT : Submodule.span B (T : Set M) = ⊤) (x : M) :
    ∃ n : ℕ, x ∈ polynomialFilteredModule v T n := by
  have hx : x ∈ Submodule.span B (T : Set M) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, polynomialFilteredModule_contains v T 0 hx⟩
  | zero => exact ⟨0, (polynomialFilteredModule v T 0).zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨max n m, (polynomialFilteredModule v T (max n m)).add_mem
      (polynomialFilteredModule_mono v T (le_max_left n m) hn)
      (polynomialFilteredModule_mono v T (le_max_right n m) hm)⟩
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece_exhaustive v hv a
    obtain ⟨m, hm⟩ := hx
    exact ⟨n + m, polynomialFilteredModule_smul v T hn hm⟩

theorem polynomialFilteredModule_map_shift (v : σ → B) (T : Submodule K M)
    (S : Submodule K N) (f : M →ₗ[B] N) (c : ℕ)
    (hf : ∀ x ∈ T, f x ∈ polynomialFilteredModule v S c) (n : ℕ) :
    (polynomialFilteredModule v T n).map (f.restrictScalars K) ≤
      polynomialFilteredModule v S (n + c) := by
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n • T at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha x hx
    change f (a • x) ∈ _
    rw [f.map_smul]
    exact polynomialFilteredModule_smul v S ha (hf x hx)
  · intro x y hx hy
    change f (x + y) ∈ _
    rw [map_add]
    exact (polynomialFilteredModule v S (n + c)).add_mem hx hy

end

/-! The degree filtration of a free rank-d module has d times the algebra filtration dimension. -/

variable {K B σ ι : Type*} [Field K] [CommRing B] [Algebra K B] [Fintype ι]

def finiteFreeConstantFrame : Submodule K (ι → B) := by
  classical
  exact Submodule.span K (Set.range (fun i : ι => Pi.single i (1 : B)))

theorem finiteFreeConstantFrame_fg : (finiteFreeConstantFrame (K := K) (B := B) (ι := ι)).FG := by
  classical
  exact Submodule.fg_span (Set.finite_range _)

theorem finiteFreeConstantFrame_scalarSpan :
    Submodule.span B (finiteFreeConstantFrame (K := K) (B := B) (ι := ι) : Set (ι → B)) = ⊤ := by
  classical
  apply top_unique
  rw [← (Pi.basisFun B ι).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, rfl⟩

theorem polynomialFilteredFree_eq_pi (v : σ → B) (n : ℕ) :
    polynomialFilteredModule v (finiteFreeConstantFrame (K := K) (B := B) (ι := ι)) n =
      Submodule.pi Set.univ (fun _ : ι => PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n) := by
  classical
  have hT : finiteFreeConstantFrame (K := K) (B := B) (ι := ι) ≤
      Submodule.pi Set.univ (fun _ : ι => (1 : Submodule K B)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    intro j _
    change (Pi.single i (1 : B) : ι → B) j ∈ (1 : Submodule K B)
    by_cases h : j = i
    · subst j
      simpa only [Pi.single_eq_same] using
        (show (1 : B) ∈ (1 : Submodule K B) from Submodule.one_le.mp le_rfl)
    · simpa only [Pi.single_eq_of_ne h] using (Submodule.zero_mem (1 : Submodule K B))
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro a ha x hx i _
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hT hx i (Set.mem_univ i))
    change a * x i ∈ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n
    rw [← hr, mul_comm, ← Algebra.smul_def]
    exact (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n).smul_mem r ha
  · intro x hx
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i _
    have h := Submodule.smul_mem_smul (hx i (Set.mem_univ i))
      (Submodule.subset_span (show Pi.single i (1 : B) ∈ Set.range (fun j : ι => Pi.single j (1 : B))
        from ⟨i, rfl⟩))
    have he : Pi.single i (x i) = x i • Pi.single i (1 : B) := by
      ext j
      by_cases hij : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne hij]
    exact he.symm ▸ h

def piSubmoduleLinearEquiv {M : Type*} [AddCommGroup M] [Module K M] (T : Submodule K M) :
    (Submodule.pi Set.univ (fun _ : ι => T)) ≃ₗ[K] (ι → T) where
  toFun x i := ⟨x.val i, x.property i (Set.mem_univ i)⟩
  invFun x := ⟨fun i => (x i).val, fun i _ => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem polynomialFilteredFree_finrank [Finite σ] (v : σ → B) (n : ℕ) :
    Module.finrank K (polynomialFilteredModule v (finiteFreeConstantFrame (K := K) (B := B) (ι := ι)) n) =
      Fintype.card ι * Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n) := by
  rw [polynomialFilteredFree_eq_pi]
  rw [(piSubmoduleLinearEquiv (ι := ι) (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n)).finrank_eq]
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

instance polynomialFilteredFree_finite [Finite σ] (v : σ → B) (n : ℕ) :
    Module.Finite K (polynomialFilteredModule v (finiteFreeConstantFrame (K := K) (B := B) (ι := ι)) n) := by
  rw [polynomialFilteredFree_eq_pi]
  exact Module.Finite.equiv
    (piSubmoduleLinearEquiv (ι := ι) (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n)).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredModuleFg.Dimension
