import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Lattice Cube Basis -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LatticeCubeBasis.Abelian

noncomputable section

/-!
Integer rounding reduces any lattice vector to the centered fundamental
cube. If that cube contains no nonzero lattice vector, a real basis of
lattice vectors is already a full integral basis.
-/

open Set _root_.Metric _root_.Submodule
open scoped Classical

variable {V Index : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype Index]

/-- A full integral basis has no nonzero lattice point in its centered
half-unit coordinate cube. This supplies the central condition for the
compactness argument from the actual central lattice basis. -/
theorem integral_basis_fundamental_cube_kernel_free
    (Λ : Submodule ℤ V) (b : Module.Basis Index ℤ Λ)
    (e : (Index → ℝ) ≃L[ℝ] V) (hbasis : ∀ i, (b i : V) = e (Pi.single i 1)) :
    ∀ t ∈ closedBall (0 : Index → ℝ) (1 / 2), e t ∈ Λ → t = 0 := by
  have hmem (i : Index) : e (Pi.single i 1) ∈ Λ := by rw [← hbasis]; exact (b i).property
  have hspan : span ℤ (Set.range (fun i => e (Pi.single i 1))) = Λ := by
    apply (span_range_subtype_eq_top_iff Λ hmem).mp
    have heq : (fun i => (⟨e (Pi.single i 1), hmem i⟩ : Λ)) = b := by
      funext i
      exact Subtype.ext (hbasis i).symm
    rw [heq]
    exact b.span_eq
  let bR : Module.Basis Index ℝ V := (Pi.basisFun ℝ Index).map e.toLinearEquiv
  have hbR : (bR : Index → V) = fun i => e (Pi.single i 1) := by
    funext i
    simp [bR, Pi.basisFun_apply]
  have hrepr (t : Index → ℝ) (i : Index) : bR.repr (e t) i = t i := by simp [bR]
  have hspanR : span ℤ (Set.range bR) = Λ := by rw [hbR]; exact hspan
  intro t ht hΛ
  have htspan : e t ∈ span ℤ (Set.range bR) := by rw [hspanR]; exact hΛ
  funext i
  obtain ⟨z, hz⟩ := (bR.mem_span_iff_repr_mem ℤ (e t)).mp htspan i
  rw [hrepr] at hz
  have hbound : |t i| ≤ (1 / 2 : ℝ) := by
    have h := (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp ht i
    simpa only [Real.dist_eq, Pi.zero_apply, sub_zero] using h
  have hzlt : |(z : ℝ)| < 1 := by
    change (z : ℝ) = t i at hz
    rw [hz]
    exact hbound.trans_lt (by norm_num)
  have hzlt' : |z| < (1 : ℤ) := by exact_mod_cast hzlt
  have hz₀ : z = 0 := by
    have h := abs_lt.mp hzlt'
    omega
  change t i = 0
  rw [← hz, hz₀]
  exact map_zero _

/-- Exclusion of nonzero lattice vectors in the centered coordinate cube
proves that the given period vectors form the full integral lattice basis. -/
theorem exists_integral_basis_of_fundamental_cube
    (Λ : Submodule ℤ V) (e : (Index → ℝ) ≃L[ℝ] V)
    (hbasis : ∀ i, e (Pi.single i 1) ∈ Λ)
    (hcube : ∀ t ∈ closedBall (0 : Index → ℝ) (1 / 2), e t ∈ Λ → t = 0) :
    ∃ b : Module.Basis Index ℤ Λ, ∀ i, (b i : V) = e (Pi.single i 1) := by
  let b : Module.Basis Index ℝ V := (Pi.basisFun ℝ Index).map e.toLinearEquiv
  have hbi (i : Index) : b i = e (Pi.single i 1) := by simp [b, Pi.basisFun_apply]
  have hrepr (t : Index → ℝ) (i : Index) : b.repr (e t) i = t i := by simp [b]
  have hspanle : span ℤ (Set.range b) ≤ Λ := by
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hbi]
    exact hbasis i
  have hle : Λ ≤ span ℤ (Set.range b) := by
    intro w hw
    let t := e.symm w
    let z : Index → ℝ := fun i => (round (t i) : ℝ)
    have hz : e z ∈ span ℤ (Set.range b) := by
      apply (b.mem_span_iff_repr_mem ℤ (e z)).mpr
      intro i
      refine ⟨round (t i), ?_⟩
      rw [hrepr]
      rfl
    have hcubeMem : t - z ∈ closedBall (0 : Index → ℝ) (1 / 2) := by
      rw [mem_closedBall, dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      intro i
      change |t i - (round (t i) : ℝ) - 0| ≤ (1 / 2 : ℝ)
      simpa only [sub_zero] using abs_sub_round (t i)
    have hmem : e (t - z) ∈ Λ := by
      rw [map_sub]
      change e (e.symm w) - e z ∈ Λ
      rw [e.apply_symm_apply]
      exact Λ.sub_mem hw (hspanle hz)
    have ht : t = z := sub_eq_zero.mp (hcube (t - z) hcubeMem hmem)
    have hez : e z = w := by rw [← ht]; exact e.apply_symm_apply w
    rw [hez] at hz
    exact hz
  have hspan : span ℤ (Set.range b) = Λ := le_antisymm hspanle hle
  let bZ := (b.restrictScalars ℤ).map (LinearEquiv.ofEq _ _ hspan)
  refine ⟨bZ, ?_⟩
  intro i
  change ((b.restrictScalars ℤ) i : V) = e (Pi.single i 1)
  rw [Module.Basis.restrictScalars_apply, hbi]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LatticeCubeBasis.Abelian
