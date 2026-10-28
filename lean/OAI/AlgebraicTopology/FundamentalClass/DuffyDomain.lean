import OAI.AlgebraicTopology.DeRham.Comparison.DuffyCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Duffy Domain -/

namespace OAI.AlgebraicTopology.FundamentalClass.DuffyDomain.IntegrationConstruction.Duffy

noncomputable section

/-! Integration: the interior change of variables from the cube to the simplex,
using the first d barycentric coordinates. -/

open Set
open scoped ContDiff

def front (d : ℕ) (t : Fin d → ℝ) (i : Fin d) : ℝ :=
  DeRham.Comparison.DuffyCoordinates.Duffy.coordinates d t i.castSucc

def cubeInterior (d : ℕ) : Set (Fin d → ℝ) := {t | ∀ i, 0 < t i ∧ t i < 1}

def simplexInterior (d : ℕ) : Set (Fin d → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

theorem front_succ (d : ℕ) (t : Fin (d + 1) → ℝ) :
    front (d + 1) t = Fin.cons (t 0) ((1 - t 0) • front d (Fin.tail t)) := by
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  rfl

theorem front_contDiff (d : ℕ) : ContDiff ℝ ∞ (front d) :=
  contDiff_pi.mpr fun i =>
    (contDiff_pi.mp (DeRham.Comparison.DuffyCoordinates.Duffy.contDiff_coordinates d ∞) i.castSucc)

theorem front_mem_simplexInterior (d : ℕ) (t : Fin d → ℝ) (ht : t ∈ cubeInterior d) :
    front d t ∈ simplexInterior d := by
  induction d with
  | zero => exact ⟨fun i => Fin.elim0 i, by simp⟩
  | succ d ih =>
    have htail : Fin.tail t ∈ cubeInterior d := fun i => ht i.succ
    have hi := ih (Fin.tail t) htail
    rw [front_succ]
    constructor
    · intro i
      refine Fin.cases (ht 0).1 (fun j => ?_) i
      exact mul_pos (sub_pos.mpr (ht 0).2) (hi.1 j)
    · change ∑ i, Fin.cons (t 0) ((1 - t 0) • front d (Fin.tail t)) i < 1
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      nlinarith [(ht 0).2, hi.2]

def inverse : (d : ℕ) → (Fin d → ℝ) → (Fin d → ℝ)
  | 0, _ => 0
  | d + 1, x => Fin.cons (x 0) (inverse d ((1 - x 0)⁻¹ • Fin.tail x))

theorem simplexInterior_zero_lt_one {d : ℕ} {x : Fin (d + 1) → ℝ}
    (hx : x ∈ simplexInterior (d + 1)) : x 0 < 1 := by
  have hsum := hx.2
  rw [Fin.sum_univ_succ] at hsum
  have htail : 0 ≤ ∑ i : Fin d, x i.succ :=
    Finset.sum_nonneg fun i _ => (hx.1 i.succ).le
  linarith

theorem normalizedTail_mem_simplexInterior {d : ℕ} {x : Fin (d + 1) → ℝ}
    (hx : x ∈ simplexInterior (d + 1)) :
    (1 - x 0)⁻¹ • Fin.tail x ∈ simplexInterior d := by
  have hp : 0 < 1 - x 0 := sub_pos.mpr (simplexInterior_zero_lt_one hx)
  constructor
  · intro i
    exact mul_pos (inv_pos.mpr hp) (hx.1 i.succ)
  · have hsum := hx.2
    rw [Fin.sum_univ_succ] at hsum
    change ∑ i : Fin d, (1 - x 0)⁻¹ * x i.succ < 1
    rw [← Finset.mul_sum, ← div_eq_inv_mul]
    exact (div_lt_one hp).mpr (by linarith)

theorem inverse_mem_cubeInterior (d : ℕ) (x : Fin d → ℝ) (hx : x ∈ simplexInterior d) :
    Duffy.inverse d x ∈ cubeInterior d := by
  induction d with
  | zero => exact fun i => Fin.elim0 i
  | succ d ih =>
    intro i
    refine Fin.cases ⟨hx.1 0, simplexInterior_zero_lt_one (x := x) hx⟩ (fun j => ?_) i
    exact ih _ (normalizedTail_mem_simplexInterior hx) j

theorem front_inverse (d : ℕ) (x : Fin d → ℝ) (hx : x ∈ simplexInterior d) :
    front d (Duffy.inverse d x) = x := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    rw [front_succ]
    have ht := ih _ (normalizedTail_mem_simplexInterior hx)
    have hn : 1 - x 0 ≠ 0 := ne_of_gt (sub_pos.mpr (simplexInterior_zero_lt_one hx))
    change Fin.cons (x 0)
      ((1 - x 0) • front d (Duffy.inverse d ((1 - x 0)⁻¹ • Fin.tail x))) = x
    rw [ht, smul_smul, mul_inv_cancel₀ hn, one_smul]
    exact Fin.cons_self_tail x

theorem inverse_front (d : ℕ) (t : Fin d → ℝ) (ht : t ∈ cubeInterior d) :
    Duffy.inverse d (front d t) = t := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    rw [front_succ]
    have hn : 1 - t 0 ≠ 0 := ne_of_gt (sub_pos.mpr (ht 0).2)
    change Fin.cons (t 0)
      (Duffy.inverse d ((1 - t 0)⁻¹ • ((1 - t 0) • front d (Fin.tail t)))) = t
    have htail : Duffy.inverse d (front d (Fin.tail t)) = Fin.tail t :=
      ih (Fin.tail t) (fun j => ht j.succ)
    rw [smul_smul, inv_mul_cancel₀ hn, one_smul, htail]
    exact Fin.cons_self_tail t

theorem front_injOn (d : ℕ) : Set.InjOn (front d) (cubeInterior d) := by
  intro x hx y hy h
  rw [← inverse_front d x hx, ← inverse_front d y hy, h]

theorem front_image (d : ℕ) : front d '' cubeInterior d = simplexInterior d := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact front_mem_simplexInterior d t ht
  · intro x hx
    exact ⟨Duffy.inverse d x, inverse_mem_cubeInterior d x hx, front_inverse d x hx⟩

end

end OAI.AlgebraicTopology.FundamentalClass.DuffyDomain.IntegrationConstruction.Duffy
