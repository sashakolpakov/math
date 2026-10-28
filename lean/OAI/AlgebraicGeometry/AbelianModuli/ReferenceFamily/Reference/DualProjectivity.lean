import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Discriminant
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Dual Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The integral dual reference lattice defines a projective torus.
A bounded denominator constructs a positive integral Hermitian form on
that lattice from the original reference form. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

theorem Fiber.ReferenceAnalyticFiber.dual_positive_integral (hP : P.IsAdmissible) :
    ∃ H : Fiber.ReferenceTangent s →ₗ⋆[ℂ] Fiber.ReferenceTangent s →ₗ[ℂ] ℂ,
      (∀ u v, H v u = star (H u v)) ∧
      (∀ u, u ≠ 0 → 0 < (H u u).re) ∧
      (∀ u ∈ F.dualLattice, ∀ v ∈ F.dualLattice, ∃ m : ℤ, (H u v).im = (m : ℝ)) := by
  obtain ⟨n, hn, hL⟩ := F.dualLattice_bounded_denominator hP
  refine ⟨(n * n) • F.form, ?_, ?_, ?_⟩
  · intro u v
    change (n * n) • F.form v u = star ((n * n) • F.form u v)
    rw [F.hermitian, star_nsmul]
  · intro u hu
    change (((n * n) • F.form u u) : ℂ).re > 0
    rw [Complex.re_nsmul, nsmul_eq_mul]
    exact mul_pos (Nat.cast_pos.mpr (Nat.mul_pos hn hn)) (F.positive u hu)
  · intro u hu v hv
    obtain ⟨a, ha⟩ := F.integralLatticeEquiv.surjective ⟨n • u, hL ⟨u, hu⟩⟩
    obtain ⟨b, hb⟩ := F.integralLatticeEquiv.surjective ⟨n • v, hL ⟨v, hv⟩⟩
    have he := F.latticeEquiv_polarization hP a b
    change (F.form (F.integralLatticeEquiv a).val (F.integralLatticeEquiv b).val).im = _ at he
    rw [ha, hb] at he
    refine ⟨P.integralForm a b, ?_⟩
    change (((n * n) • F.form u v) : ℂ).im = _
    have hscale : F.form (n • u) (n • v) = (n * n) • F.form u v := by
      have hfirst := congrArg (fun l : Fiber.ReferenceTangent s →ₗ[ℂ] ℂ => l (n • v))
        (map_nsmul F.form.toAddMonoidHom n u)
      have hsecond := map_nsmul (F.form u).toAddMonoidHom n v
      exact hfirst.trans ((congrArg (fun w : ℂ => n • w) hsecond).trans (smul_smul n n _))
    exact (congrArg Complex.im hscale).symm.trans he

instance Fiber.ReferenceAnalyticFiber.dualTorus_compact : CompactSpace (Fiber.ReferenceTangent s ⧸ F.dualLattice.toAddSubgroup) := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic F.dualLattice
    (QuotientAddGroup.mk : Fiber.ReferenceTangent s → Fiber.ReferenceTangent s ⧸ F.dualLattice.toAddSubgroup)
    QuotientAddGroup.continuous_mk (by
      intro u v hv
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff v).mpr hv, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

theorem Fiber.ReferenceAnalyticFiber.dualTorus_projective (hP : P.IsAdmissible) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus (Fiber.ReferenceTangent s) F.dualLattice.toAddSubgroup := by
  let : DiscreteTopology F.dualLattice.toAddSubgroup := F.dualLattice_discrete
  exact (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (Fiber.ReferenceTangent s)
    F.dualLattice.toAddSubgroup).mpr (F.dual_positive_integral hP)

def Fiber.ReferenceAnalyticFiber.dualPeriodData (hP : P.IsAdmissible) : RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData where
  space := Fiber.ReferenceTangent s
  periodIntegerLattice := F.dualLattice
  periodIntegerLattice_discrete := F.dualLattice_discrete
  periodIntegerLattice_full := F.dualLattice_full
  projective := F.dualTorus_projective hP

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
