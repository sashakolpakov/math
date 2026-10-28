import OAI.AlgebraicGeometry.DivisorClass.Chern.FubiniStudyGeneratedMultiple
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GeneratedTwist

/-! # Twist Global Generation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.TwistGlobalGeneration

noncomputable section

/-! The actual original holomorphic bundle has a genuinely globally generated positive twist. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem exists_positiveHolomorphicTwist_globally_generated (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) :
    ∃ n : ℕ, 0 < n ∧ HolomorphicSection.Fin.holomorphicLineGloballyGenerated (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) := by
  have HG := FubiniStudyGeneratedMultiple.exists_fubiniStudyTwist_globally_generated_multiple V
  let N := HG.choose
  have hN : 0 < N := HG.choose_spec.1
  have hG := HG.choose_spec.2
  have Hlocal (x : V.analyticSpace) :
      ∃ k : ℕ, ∃ s : HolomorphicSection.Data.HolomorphicLineSection (u + k • (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)) ⊤,
        HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt (u + k • (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)) s x := by
    have H := PointLogSolverNonzero.positiveHolomorphicTwist_nonzero_at_point V h x
    let k := H.choose
    have hk : k ≤ k * N := by
      calc
        k = k * 1 := (Nat.mul_one k).symm
        _ ≤ k * N := Nat.mul_le_mul_left k hN
    have HS := H.choose_spec.2 (k * N) hk
    have heq : u + (k * N) • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V = u + k • (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) := by
      rw [smul_smul]
    exact ⟨k, HolomorphicSection.Fin.holomorphicSectionCast heq HS.choose,
      HolomorphicSection.Fin.holomorphicSectionCast_nonzero heq HS.choose x HS.choose_spec⟩
  have HT := Holomorphic.GeneratedTwist.exists_holomorphic_globally_generated_twist u (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) hG Hlocal
  have heq : u + HT.choose • (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) =
      u + (HT.choose * N) • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V := by rw [smul_smul]
  exact ⟨HT.choose * N, Nat.mul_pos HT.choose_spec.1 hN, heq ▸ HT.choose_spec.2⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.TwistGlobalGeneration
