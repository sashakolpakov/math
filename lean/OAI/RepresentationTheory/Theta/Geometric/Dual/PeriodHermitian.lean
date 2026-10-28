import OAI.RepresentationTheory.Theta.Geometric.Period.DualQuotient

/-! # Period Hermitian -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A positive integral Hermitian form on the dual period lattice. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.dualPeriod_positive_integral (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    ∃ H : (D.canonicalPeriodData hg x).space →ₗ⋆[ℂ]
        (D.canonicalPeriodData hg x).space →ₗ[ℂ] ℂ,
      (∀ u v, H v u = star (H u v)) ∧
      (∀ u, u ≠ 0 → 0 < (H u u).re) ∧
      (∀ u ∈ D.periodDualLattice hg x, ∀ v ∈ D.periodDualLattice hg x,
        ∃ m : ℤ, (H u v).im = (m : ℝ)) := by
  obtain ⟨n, hn, hL⟩ := D.periodDualLattice_bounded_denominator hg x
  refine ⟨(n * n) • D.periodHermitian hg x, ?_, ?_, ?_⟩
  · intro u v
    change (n * n) • D.periodHermitian hg x v u =
      star ((n * n) • D.periodHermitian hg x u v)
    rw [D.periodHermitian_hermitian hg x u v, star_nsmul]
  · intro u hu
    have hp := D.periodHermitian_positive hg x u hu
    change (((n * n) • D.periodHermitian hg x u u) : ℂ).re > 0
    rw [Complex.re_nsmul, nsmul_eq_mul]
    exact mul_pos (Nat.cast_pos.mpr (Nat.mul_pos hn hn)) hp
  · intro u hu v hv
    obtain ⟨a, ha⟩ := (D.periodLatticeEquiv hg x).surjective ⟨n • u, hL ⟨u, hu⟩⟩
    obtain ⟨b, hb⟩ := (D.periodLatticeEquiv hg x).surjective ⟨n • v, hL ⟨v, hv⟩⟩
    have he := D.periodImaginaryForm_integral hg x a b
    have ha' := congrArg Subtype.val ha
    have hb' := congrArg Subtype.val hb
    change D.periodReferenceEmbedding x.val a.val = n • u at ha'
    change D.periodReferenceEmbedding x.val b.val = n • v at hb'
    change (D.periodHermitian hg x (D.periodReferenceEmbedding x.val a.val)
      (D.periodReferenceEmbedding x.val b.val)).im = _ at he
    rw [ha', hb'] at he
    change (D.periodHermitian hg x (n • (u : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)))
      (n • (v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)))).im = _ at he
    refine ⟨D.pel.reference.integralForm a b, ?_⟩
    change (((n * n) • D.periodHermitian hg x u v) : ℂ).im = _
    have hscale : D.periodHermitian hg x (n • u) (n • v) =
        (n * n) • D.periodHermitian hg x u v := by
      have hfirst := congrArg (fun l : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →ₗ[ℂ] ℂ => l (n • v))
        (map_nsmul (D.periodHermitian hg x).toAddMonoidHom n u)
      have hsecond := map_nsmul (D.periodHermitian hg x u).toAddMonoidHom n v
      exact hfirst.trans ((congrArg (fun z : ℂ => n • z) hsecond).trans (smul_smul n n _))
    exact (congrArg Complex.im hscale).symm.trans he

end

end OAI.RepresentationTheory.Theta.Geometric
