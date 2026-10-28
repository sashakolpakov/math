import OAI.RepresentationTheory.Theta.Geometric.Torus.Data
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Doubled Period Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Doubling the period lattice permits the original Hermitian form to be
halved in the theta construction while preserving its integral periods. -/

variable (Φ : Torus.Data.CM.ProjectivePeriodData)

def Torus.Data.CM.ProjectivePeriodData.halfLinearEquiv : Φ.space ≃L[ℝ] Φ.space where
  toFun z := (1 / 2 : ℝ) • z
  invFun z := (2 : ℝ) • z
  map_add' := smul_add _
  map_smul' a z := smul_comm _ _ _
  left_inv z := by simp only [smul_smul]; norm_num
  right_inv z := by simp only [smul_smul]; norm_num
  continuous_toFun := continuous_const_smul _
  continuous_invFun := continuous_const_smul _

def Torus.Data.CM.ProjectivePeriodData.doubledLattice : Submodule ℤ Φ.space :=
  ZLattice.comap ℝ Φ.periodIntegerLattice Φ.halfLinearEquiv.toLinearMap

instance Torus.Data.CM.ProjectivePeriodData.doubledLattice_discrete : DiscreteTopology Φ.doubledLattice :=
  inferInstanceAs (DiscreteTopology
    (ZLattice.comap ℝ Φ.periodIntegerLattice Φ.halfLinearEquiv.toLinearMap))

instance Torus.Data.CM.ProjectivePeriodData.doubledLattice_full : IsZLattice ℝ Φ.doubledLattice :=
  inferInstanceAs (IsZLattice ℝ
    (ZLattice.comap ℝ Φ.periodIntegerLattice Φ.halfLinearEquiv.toLinearMap))

instance Torus.Data.CM.ProjectivePeriodData.doubledPeriodTorus_compact : CompactSpace (Φ.space ⧸ Φ.doubledLattice.toAddSubgroup) := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic Φ.doubledLattice
    (QuotientAddGroup.mk : Φ.space → Φ.space ⧸ Φ.doubledLattice.toAddSubgroup)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

theorem Torus.Data.CM.ProjectivePeriodData.mem_doubledLattice (z : Φ.space) :
    z ∈ Φ.doubledLattice ↔ ∃ l : Φ.periodIntegerLattice, (2 : ℕ) • l.val = z := by
  constructor
  · intro hz
    refine ⟨⟨(1 / 2 : ℝ) • z, hz⟩, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    norm_num
  · rintro ⟨l, rfl⟩
    change (1 / 2 : ℝ) • (2 : ℕ) • l.val ∈ Φ.periodIntegerLattice
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    norm_num

def Torus.Data.CM.ProjectivePeriodData.halfHermitian (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ) :
    Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ := (1 / 2 : ℂ) • H

theorem Torus.Data.CM.ProjectivePeriodData.halfHermitian_symm (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)
    (hsym : ∀ u v, H v u = star (H u v)) :
    ∀ u v, Φ.halfHermitian H v u = star (Φ.halfHermitian H u v) := by
  intro u v
  change (1 / 2 : ℂ) * H v u = star ((1 / 2 : ℂ) * H u v)
  rw [hsym, star_mul]
  simp [mul_comm]

theorem Torus.Data.CM.ProjectivePeriodData.halfHermitian_positive (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)
    (hpos : ∀ u, u ≠ 0 → 0 < (H u u).re) :
    ∀ u, u ≠ 0 → 0 < (Φ.halfHermitian H u u).re := by
  intro u hu
  change 0 < ((1 / 2 : ℂ) * H u u).re
  simp only [one_div, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.re_ofNat,
    Complex.im_ofNat, neg_zero, zero_div, zero_mul, sub_zero]
  norm_num
  exact hpos u hu

theorem Torus.Data.CM.ProjectivePeriodData.halfHermitian_integral (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)
    (hint : ∀ u ∈ Φ.periodIntegerLattice, ∀ v ∈ Φ.periodIntegerLattice,
      ∃ m : ℤ, (H u v).im = (m : ℝ)) :
    ∀ u ∈ Φ.doubledLattice, ∀ v ∈ Φ.doubledLattice,
      ∃ m : ℤ, (Φ.halfHermitian H u v).im = (m : ℝ) := by
  intro u hu v hv
  obtain ⟨l, rfl⟩ := (Φ.mem_doubledLattice u).mp hu
  obtain ⟨m, rfl⟩ := (Φ.mem_doubledLattice v).mp hv
  obtain ⟨a, ha⟩ := hint l.val l.property m.val m.property
  refine ⟨2 * a, ?_⟩
  change ((1 / 2 : ℂ) * H ((2 : ℕ) • l.val) ((2 : ℕ) • m.val)).im = _
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, ← mul_assoc]
  norm_num
  rw [ha]

end

end OAI.RepresentationTheory.Theta.Geometric
