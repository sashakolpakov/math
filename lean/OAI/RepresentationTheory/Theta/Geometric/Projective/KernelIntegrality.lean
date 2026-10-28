import OAI.RepresentationTheory.Theta.Geometric.Projective.RationalKernel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates

/-! # Kernel Integrality -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The entire projective kernel is integral at every split local block:
its scalar cube roots of unity have local norm one. -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.projective_kernel_local_integral (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU)
    (h : ∀ x : D.domain, D.periodMap g x.val = x.val) (v : Fin s × Bool) :
    D.localMatrix v g ∈ SphericalGU.Spherical.integralSL3 q := by
  have hs := D.rational_period_kernel_scalar hg g h
  have hc := D.rational_period_kernel_cube hg g h
  have hp : (D.localEmbedding v (g.val.val 2 2)) ^ 3 = 1 := by
    rw [← map_pow, hc, map_one]
  have hn : ‖D.localEmbedding v (g.val.val 2 2)‖ ≤ 1 := by
    apply (pow_le_one_iff_of_nonneg (norm_nonneg _) (by decide : 3 ≠ 0)).mp
    rw [← norm_pow, hp, norm_one]
  apply (AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport.integralSL3_iff_entries q _).mpr
  intro i j
  change ‖D.localEmbedding v (g.val.val i j)‖ ≤ 1
  have he := congrFun (congrFun hs i) j
  rw [he]
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using hn
  · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, map_zero, norm_zero, zero_le_one]

theorem Data.ActiveHeckeThetaData.projective_kernel_active_integral (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU)
    (h : ∀ x : D.domain, D.periodMap g x.val = x.val) :
    D.activeLocal g ∈ SphericalGU.Spherical.integralSL3 q :=
  D.projective_kernel_local_integral hg g h (D.pel.reference.distinguished, false)

end

end OAI.RepresentationTheory.Theta.Geometric
