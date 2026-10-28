import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralSymplectic
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan

/-! # Local Matrices -/

namespace OAI.RepresentationTheory.Theta.Geometric.Cleared.LocalMatrices

noncomputable section

/-! Exact entry bounds for centrally cleared active double cosets,
including their inverses. -/

set_option backward.isDefEq.respectTransparency false
open scoped Classical

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan

theorem inDoubleCoset_of_quotient_eq {G : Type*} [Group G] (K : Subgroup G)
    {a g h : G} (he : (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk h)
    (hh : DoubleCosets.Spherical.InDoubleCoset K a h) : DoubleCosets.Spherical.InDoubleCoset K a g := by
  obtain ⟨u, v, rfl⟩ := hh
  have ht : g⁻¹ * (u.val * a * v.val) ∈ K := (QuotientGroup.eq.mp he)
  refine ⟨u, v * ⟨(g⁻¹ * (u.val * a * v.val))⁻¹, K.inv_mem ht⟩, ?_⟩
  change g = u.val * a * (v.val * (g⁻¹ * (u.val * a * v.val))⁻¹)
  group

theorem inDoubleCoset_inv {G : Type*} [Group G] (K : Subgroup G)
    {a g : G} (h : DoubleCosets.Spherical.InDoubleCoset K a g) :
    DoubleCosets.Spherical.InDoubleCoset K a⁻¹ g⁻¹ := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨v⁻¹, u⁻¹, by simp only [mul_inv_rev, Subgroup.coe_inv, mul_assoc]⟩

variable (q : ℕ) [Fact q.Prime]

theorem scaled_doubleCoset_entries (n : ℕ) (a g : SphericalGU.Spherical.SL3 q)
    (ha : ∀ i j, ‖(q : ℚ_[q]) ^ n * a.val i j‖ ≤ 1)
    (hg : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q) a g) :
    ∀ i j, ‖(q : ℚ_[q]) ^ n * g.val i j‖ ≤ 1 := by
  obtain ⟨u, v, rfl⟩ := hg
  have hu := (AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport.integralSL3_iff_entries q u.val).mp u.property
  have hv := (AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport.integralSL3_iff_entries q v.val).mp v.property
  have H := AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralSymplectic.Local.padic_matrix_mul_integral q
    (u.val.val * ((q : ℚ_[q]) ^ n • a.val)) v.val.val
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralSymplectic.Local.padic_matrix_mul_integral q u.val.val ((q : ℚ_[q]) ^ n • a.val) hu ha) hv
  rw [Matrix.mul_smul, Matrix.smul_mul] at H
  exact H

theorem active_clearing_bounds {s : ℕ} (v : Fin s) (a : Intrinsic.Hecke.ActiveWeight) (i : Fin 3) :
    0 ≤ a.val i + (Intrinsic.Hecke.clearingExponent v a : ℤ) ∧
      0 ≤ -a.val i + (Intrinsic.Hecke.clearingExponent v a : ℤ) := by
  have h := (Intrinsic.Hecke.clearedActiveType v a).property.2 v i
  change 0 ≤ (if v = v then a.val i else 0) + (Intrinsic.Hecke.clearingExponent v a : ℤ) ∧
    (if v = v then a.val i else 0) + (Intrinsic.Hecke.clearingExponent v a : ℤ) ≤
      0 + 2 * (Intrinsic.Hecke.clearingExponent v a : ℤ) at h
  rw [ite_eq_left rfl] at h
  omega

theorem active_representative_cleared_entries {s : ℕ} (v : Fin s) (a : Intrinsic.Hecke.ActiveWeight) :
    ∀ i j, ‖(q : ℚ_[q]) ^ Intrinsic.Hecke.clearingExponent v a * (Intrinsic.Hecke.activeSLRepresentative q a).val i j‖ ≤ 1 := by
  intro i j
  by_cases hij : i = j
  · subst j
    have he : (q : ℚ_[q]) ^ Intrinsic.Hecke.clearingExponent v a * (Intrinsic.Hecke.activeSLRepresentative q a).val i i =
        (q : ℚ_[q]) ^ (a.val i + (Intrinsic.Hecke.clearingExponent v a : ℤ)) := by
      simp only [Intrinsic.Hecke.activeSLRepresentative, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, Matrix.diagonal_apply_eq, Units.val_zpow_eq_zpow_val]
      change (q : ℚ_[q]) ^ Intrinsic.Hecke.clearingExponent v a * (q : ℚ_[q]) ^ a.val i = _
      rw [zpow_add₀ (by exact_mod_cast (Fact.out : q.Prime).ne_zero), zpow_natCast, mul_comm]
    rw [he]
    obtain ⟨b, hb⟩ := (AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan.q_zpow_integral_iff q _).mpr (active_clearing_bounds v a i).1
    rw [← hb]
    exact b.property
  · simp [Intrinsic.Hecke.activeSLRepresentative, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, Matrix.diagonal_apply_ne _ hij]

theorem active_representative_inverse_cleared_entries {s : ℕ} (v : Fin s) (a : Intrinsic.Hecke.ActiveWeight) :
    ∀ i j, ‖(q : ℚ_[q]) ^ Intrinsic.Hecke.clearingExponent v a * ((Intrinsic.Hecke.activeSLRepresentative q a)⁻¹).val i j‖ ≤ 1 := by
  have he : ((Intrinsic.Hecke.activeSLRepresentative q a)⁻¹).val =
      Matrix.diagonal (fun i => (q : ℚ_[q]) ^ (-a.val i)) := by
    have hs : Matrix.SpecialLinearGroup.toGL (Intrinsic.Hecke.activeSLRepresentative q a) =
        AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a.val i) := Units.ext rfl
    have h := congrArg Units.val (map_inv Matrix.SpecialLinearGroup.toGL (Intrinsic.Hecke.activeSLRepresentative q a))
    rw [hs] at h
    change ((Intrinsic.Hecke.activeSLRepresentative q a)⁻¹).val = _ at h
    rw [h]
    simp [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, zpow_neg, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit]
  rw [he]
  intro i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, ← zpow_natCast (q : ℚ_[q]), ← zpow_add₀ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)]
    obtain ⟨b, hb⟩ := (AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan.q_zpow_integral_iff q ((Intrinsic.Hecke.clearingExponent v a : ℤ) + -a.val i)).mpr
      (by have := (active_clearing_bounds v a i).2; omega)
    rw [← hb]
    exact b.property
  · simp [Matrix.diagonal_apply_ne _ hij]

end

end OAI.RepresentationTheory.Theta.Geometric.Cleared.LocalMatrices
