import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke

/-! # Compact -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Compact

noncomputable section

/-! Compactly supported locally constant functions fixed by the actual
integral SL3 group are exactly radial inputs. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

theorem compact_outer_radius (f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) (hf : HasCompactSupport f) :
    ∃ m : ℤ, ∀ x, Hecke.radius q m < ‖x‖ → f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall (0 : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R
    (by exact_mod_cast (Fact.out : q.Prime).one_lt : 1 < (q : ℝ))
  have hn' : R < Hecke.radius q (-(n : ℤ)) := by simpa [Hecke.radius] using hn
  refine ⟨-(n : ℤ), ?_⟩
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hbound := hR hmem
  have hnorm : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound
  exact (not_le_of_gt (hn'.trans hx)) hnorm

theorem locallyConstant_inner_radius (f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) (hf : IsLocallyConstant f) :
    ∃ n : ℤ, ∀ x, ‖x‖ ≤ Hecke.radius q n → f x = f 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually_eq 0)
  have hq : 1 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  have hn' : Hecke.radius q n < ε := by simpa [Hecke.radius, zpow_neg, inv_pow] using hn
  refine ⟨n, ?_⟩
  intro x hx
  apply hball
  simpa only [Metric.mem_ball, dist_zero_right] using hx.trans_lt hn'

theorem norm_radial_compact_mem (f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ)
    (hnorm : ∀ x y, ‖x‖ = ‖y‖ → f x = f y)
    (hlc : IsLocallyConstant f) (hc : HasCompactSupport f) : f ∈ RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q := by
  obtain ⟨m, hout⟩ := compact_outer_radius q f hc
  obtain ⟨n, hin⟩ := locallyConstant_inner_radius q f hlc
  let N := (max m n - m).toNat
  have hN : m + (N : ℤ) = max m n := by dsimp [N]; omega
  apply Hecke.radial_mem_of_bands q N m f hnorm hout
  intro x hx
  apply hin
  rw [hN] at hx
  exact hx.trans (Hecke.radius_antitone q (le_max_right m n))

theorem integral_fixed_compact_mem
    (f : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q))
    (hlc : IsLocallyConstant f.val) (hc : HasCompactSupport f.val) : f.val ∈ RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q :=
  norm_radial_compact_mem q f.val (Hecke.integral_fixed_eq_of_norm_eq q f) hlc hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Compact
