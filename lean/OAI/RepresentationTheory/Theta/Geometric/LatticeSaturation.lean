import OAI.RepresentationTheory.Theta.Geometric.PadicPowerSaturation
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.Submodule

/-! # Lattice Saturation -/

namespace OAI.RepresentationTheory.Theta.Geometric.LatticeSaturation

noncomputable section

/-! A full rational lattice is recovered by intersecting its q-adic
completed span with its original lattice after inverting q. -/

open scoped TensorProduct

variable {V W I : Type*} [AddCommGroup V] [Module ℚ V]
    (q : ℕ) [Fact q.Prime] [AddCommGroup W] [Module ℚ_[q] W]
    [Module ℤ_[q] W] [IsScalarTower ℤ_[q] ℚ_[q] W]
    (b : Module.Basis I ℚ V) (L : Submodule ℤ V)
    (hL : Submodule.span ℤ (Set.range b) = L)
    (e : (ℚ_[q] ⊗[ℚ] V) ≃ₗ[ℚ_[q]] W)

include hL

theorem completedLattice_coordinate_integral (i : I) (w : W)
    (hw : w ∈ Submodule.span ℤ_[q] ((fun v => e (1 ⊗ₜ[ℚ] v)) '' (L : Set V))) :
    ((b.baseChange ℚ_[q]).repr (e.symm w)) i ∈ Set.range (algebraMap ℤ_[q] ℚ_[q]) := by
  let l : W →ₗ[ℤ_[q]] ℚ_[q] :=
    (((b.baseChange ℚ_[q]).coord i).comp e.symm.toLinearMap).restrictScalars ℤ_[q]
  let J : Submodule ℤ_[q] ℚ_[q] := (Algebra.linearMap ℤ_[q] ℚ_[q]).range
  change l w ∈ J
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, hv, rfl⟩ := hw
    have hc := (b.mem_span_iff_repr_mem ℤ v).mp (hL.symm ▸ hv) i
    obtain ⟨z, hz⟩ := hc
    refine ⟨(z : ℤ_[q]), ?_⟩
    change algebraMap ℤ_[q] ℚ_[q] (z : ℤ_[q]) =
      (b.baseChange ℚ_[q]).repr (e.symm (e (1 ⊗ₜ[ℚ] v))) i
    rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, ← hz]
    simp
  | zero =>
    rw [map_zero]
    exact J.zero_mem
  | add u v _ _ hu hv =>
    rw [map_add]
    exact J.add_mem hu hv
  | smul a u _ hu =>
    rw [map_smul]
    exact J.smul_mem a hu

theorem completedLattice_rational_coordinate_norm (v : V)
    (hv : e (1 ⊗ₜ[ℚ] v) ∈ Submodule.span ℤ_[q]
      ((fun x => e (1 ⊗ₜ[ℚ] x)) '' (L : Set V))) (i : I) :
    ‖((b.repr v i : ℚ) : ℚ_[q])‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := completedLattice_coordinate_integral q b L hL e i _ hv
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul] at ha
  have he : (a : ℚ_[q]) = ((b.repr v i : ℚ) : ℚ_[q]) := by simpa using ha
  rw [← he]
  exact a.property

theorem completedLattice_power_saturation (v : V)
    (hv : e (1 ⊗ₜ[ℚ] v) ∈ Submodule.span ℤ_[q]
      ((fun x => e (1 ⊗ₜ[ℚ] x)) '' (L : Set V)))
    (hn : ∃ n : ℕ, (q : ℤ) ^ n • v ∈ L) : v ∈ L := by
  have hc (x : V) : x ∈ L ↔ ∀ i, b.repr x i ∈ Set.range (algebraMap ℤ ℚ) := by
    rw [← hL]
    exact b.mem_span_iff_repr_mem ℤ x
  apply (hc v).mpr
  intro i
  obtain ⟨n, hn⟩ := hn
  obtain ⟨z, hz⟩ := (hc _).mp hn i
  have hz' : (q : ℚ) ^ n * b.repr v i = z := by
    rw [map_zsmul, Finsupp.smul_apply] at hz
    simpa only [Algebra.algebraMap_eq_smul_one, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast,
      mul_one] using hz.symm
  obtain ⟨z, hz⟩ := PadicPowerSaturation.rational_power_saturation q (b.repr v i)
    (completedLattice_rational_coordinate_norm q b L hL e v hv i) n z hz'
  exact ⟨z, hz.symm⟩

end

end OAI.RepresentationTheory.Theta.Geometric.LatticeSaturation
