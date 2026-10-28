import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodCM

/-! # Period Inverse -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Inverse rational SU matrices induce inverse maps of the actual period
quotient tangent spaces. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.periodMap_inv_apply (g : D.RationalSU) (z : LinearTheta.BallCoordinates) :
    D.periodMap g⁻¹ (D.periodMap g z) = z := by
  change Period.Ne.rationalPeriodPerm D.pel.reference.b D.pel.reference.μ g⁻¹
    (Period.Ne.rationalPeriodPerm D.pel.reference.b D.pel.reference.μ g z) = z
  rw [map_inv]
  exact Equiv.symm_apply_apply _ _

theorem Data.ActiveHeckeThetaData.rationalAtEmbedding_inv_apply (σ : E →+* ℂ) (g : D.RationalSU) (v : Period.Quotient.PeriodBlock) :
    D.rationalAtEmbedding σ g⁻¹ (D.rationalAtEmbedding σ g v) = v := by
  change Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map σ g.val⁻¹)
    (Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map σ g.val) v) = v
  rw [map_inv, map_inv]
  exact LinearEquiv.symm_apply_apply _ _

theorem Data.ActiveHeckeThetaData.rationalAmbient_inv_apply (g : D.RationalSU) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    D.rationalAmbient g⁻¹ (D.rationalAmbient g u) = u := by
  funext i
  apply Prod.ext
  · exact D.rationalAtEmbedding_inv_apply _ g (u i).1
  · exact D.rationalAtEmbedding_inv_apply _ g (u i).2

theorem Data.ActiveHeckeThetaData.rationalPeriodLinear_inverse (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.rationalPeriodLinear g⁻¹ ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩
      (D.rationalPeriodLinear g x t) = t := by
  let y : D.domain := ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩
  change D.rationalPeriodLinear g⁻¹ y
    (D.periodProjection y.val (D.rationalAmbient g (D.periodSection t))) = t
  rw [D.rationalPeriodLinear_projection hg, D.rationalAmbient_inv_apply]
  change D.periodProjection (D.periodMap g⁻¹ (D.periodMap g x.val)) (D.periodSection t) = t
  rw [D.periodMap_inv_apply, D.periodProjection_section hg]

theorem Data.ActiveHeckeThetaData.rationalPeriodLinear_right_inverse (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.rationalPeriodLinear g x
      (D.rationalPeriodLinear g⁻¹ ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩ t) = t := by
  let y : D.domain := ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩
  have h := D.rationalPeriodLinear_inverse hg g⁻¹ y t
  have hx : (⟨D.periodMap g⁻¹ y.val, D.periodMap_preserves g⁻¹ y.val y.property⟩ : D.domain) = x :=
    Subtype.ext (D.periodMap_inv_apply g x.val)
  simpa only [inv_inv, hx] using h

theorem Data.ActiveHeckeThetaData.cleared_rationalPeriodLinear_complement (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (n m : ℕ) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    ((q : ℤ) ^ m • D.rationalPeriodLinear g⁻¹
      ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩)
      (((q : ℤ) ^ n • D.rationalPeriodLinear g x) t) = q ^ (n + m) • t := by
  change (q : ℤ) ^ m • D.rationalPeriodLinear g⁻¹ _
    ((q : ℤ) ^ n • D.rationalPeriodLinear g x t) = _
  rw [map_zsmul, D.rationalPeriodLinear_inverse hg, smul_smul, ← pow_add,
    Nat.add_comm m n, ← Nat.cast_pow, natCast_zsmul]

theorem Data.ActiveHeckeThetaData.cleared_rationalPeriodLinear_right_complement (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (n m : ℕ) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    ((q : ℤ) ^ n • D.rationalPeriodLinear g x)
      (((q : ℤ) ^ m • D.rationalPeriodLinear g⁻¹
        ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩) t) = q ^ (n + m) • t := by
  change (q : ℤ) ^ n • D.rationalPeriodLinear g x
    ((q : ℤ) ^ m • D.rationalPeriodLinear g⁻¹ _ t) = _
  rw [map_zsmul, D.rationalPeriodLinear_right_inverse hg, smul_smul, ← pow_add,
    ← Nat.cast_pow, natCast_zsmul]

end

end OAI.RepresentationTheory.Theta.Geometric
