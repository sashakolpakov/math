import OAI.RepresentationTheory.Theta.Geometric.Rational.ModuliMapRigidity
import OAI.RepresentationTheory.Theta.Geometric.Projective.KernelIntegrality
import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodInverse

/-! # Coset Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Equality of the original rational moduli target maps forces equality
of the literal inverse right cosets at the active split place. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.periodMap_mul_apply (g h : D.RationalSU) (x : LinearTheta.BallCoordinates) :
    D.periodMap (g * h) x = D.periodMap g (D.periodMap h x) := by
  change Period.Ne.rationalPeriodPerm D.pel.reference.b D.pel.reference.μ (g * h) x = _
  rw [map_mul]
  rfl

theorem Data.ActiveHeckeThetaData.rational_moduli_map_inverse_coset
    (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (g h : D.RationalSU)
    (he : ∀ x, D.referenceModuliMap hg (D.rationalPeriodPoint g x) =
      D.referenceModuliMap hg (D.rationalPeriodPoint h x)) :
    (QuotientGroup.mk (D.activeLocal g)⁻¹ : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) =
      QuotientGroup.mk (D.activeLocal h)⁻¹ := by
  obtain ⟨γ, hγ, hcompare⟩ := D.rational_moduli_map_arithmetic_comparison hg hc hgood hdegree g h he
  have hγlocal : D.activeLocal γ ∈ SphericalGU.Spherical.integralSL3 q := hγ.1
  have haction (x : D.domain) : D.periodMap h x.val = D.periodMap (γ * g) x.val :=
    (hcompare x).trans (D.periodMap_mul_apply γ g x.val).symm
  have hkernel : ∀ x : D.domain, D.periodMap (h * (γ * g)⁻¹) x.val = x.val := by
    intro x
    rw [D.periodMap_mul_apply]
    rw [haction ⟨D.periodMap (γ * g)⁻¹ x.val, D.periodMap_preserves _ x.val x.property⟩]
    simpa only [inv_inv] using D.periodMap_inv_apply (γ * g)⁻¹ x.val
  have hi := D.projective_kernel_active_integral hg (h * (γ * g)⁻¹) hkernel
  have H := (SphericalGU.Spherical.integralSL3 q).mul_mem hi hγlocal
  simp only [map_mul, map_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at H
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  simpa only [inv_inv] using H

end

end OAI.RepresentationTheory.Theta.Geometric
