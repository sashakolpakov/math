import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

/-! # Quotient Compact -/

namespace OAI.Geometry.ComplexBall.QuotientCompact.Arithmetic

noncomputable section

/-! Compactness descends from G/Γ to the orbit quotient Γ\\Ball, using the
inverse orbit map so that right cosets match the left action. -/

open scoped Classical
open _root_.Topology

section Quotient
variable {G X : Type*} [Group G] [MulAction G X]

def inverseOrbitQuotient (Γ : Subgroup G) (x : X) : G ⧸ Γ → MulAction.orbitRel.Quotient Γ X :=
  Quotient.lift (fun g => Quotient.mk _ (g⁻¹ • x)) (by
    intro g h hgh
    apply Quotient.sound
    change ∃ γ : Γ, γ • (h⁻¹ • x) = g⁻¹ • x
    refine ⟨⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hgh⟩, ?_⟩
    change (g⁻¹ * h) • (h⁻¹ • x) = g⁻¹ • x
    rw [← mul_smul, mul_inv_cancel_right])

lemma inverseOrbitQuotient_surjective [MulAction.IsPretransitive G X]
    (Γ : Subgroup G) (x : X) : Function.Surjective (inverseOrbitQuotient Γ x) := by
  intro y
  induction y using Quotient.inductionOn with
  | h y =>
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    refine ⟨QuotientGroup.mk g⁻¹, ?_⟩
    change Quotient.mk _ ((g⁻¹)⁻¹ • x) = Quotient.mk _ y
    rw [inv_inv, hg]

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [ContinuousSMul G X]

lemma inverseOrbitQuotient_continuous (Γ : Subgroup G) (x : X) :
    Continuous (inverseOrbitQuotient Γ x) :=
  (continuous_quotient_mk'.comp (continuous_inv.smul continuous_const)).quotient_lift _

lemma compact_orbitQuotient_of_compact_cosets [MulAction.IsPretransitive G X]
    (Γ : Subgroup G) (x : X) [CompactSpace (G ⧸ Γ)] :
    CompactSpace (MulAction.orbitRel.Quotient Γ X) := by
  constructor
  rw [← Set.range_eq_univ.mpr (inverseOrbitQuotient_surjective Γ x)]
  exact isCompact_range (inverseOrbitQuotient_continuous Γ x)

end Quotient

lemma ballQuotient_compact (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0)
    (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b)) [CompactSpace (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b ⧸ Γ)] :
    CompactSpace (MulAction.orbitRel.Quotient Γ (ArithmeticQuotientBoostBall.Ball b)) := by
  let : MulAction.IsPretransitive (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (ArithmeticQuotientBoostBall.Ball b) :=
    ArithmeticQuotientBoostBall.ballAction_pretransitive b hbim hb
  exact compact_orbitQuotient_of_compact_cosets Γ (ArithmeticQuotientBoostBall.ballOrigin b hb)

end

end OAI.Geometry.ComplexBall.QuotientCompact.Arithmetic
