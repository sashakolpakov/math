import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ZeroCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicBoundaryIntegralSequence

/-! # Permissibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Permissibility.Construction

noncomputable section

/-! The global coefficient ideal detects every smooth center inside the carrier, including the zero-coefficient center step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem smooth_global_center_iff_coefficient_center
    {X : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J H : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (hHI : H ≤ I) (b : ℕ) (hb : 0 < b) :
    J ≤ I ^ b ↔ CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι ≤ (I.comap H.subschemeι) ^ b.factorial := by
  constructor
  · exact CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_le_of_order f I J b H.subschemeι
  · intro hC
    let q := Scheme.IdealSheafData.inclusion hHI
    have hq : q ≫ H.subschemeι = I.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι hHI
    have h := Scheme.IdealSheafData.comap_mono q hC
    change (CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι).comap q ≤
      ((I.comap H.subschemeι) ^ b.factorial).comap q at h
    rw [CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_comap, hq, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow,
      ← Scheme.IdealSheafData.comap_comp, hq] at h
    have hI : I.comap I.subschemeι = ⊥ := (ZeroCenter.Construction.idealSheaf_comap_subscheme_eq_bot_iff I I).mpr le_rfl
    rw [hI] at h
    apply (ZeroCenter.Construction.smoothCoefficientIdealSheaf_eq_bot_iff f J I b hb).mp
    apply le_bot_iff.mp (h.trans _)
    intro U
    change (⊥ : Ideal Γ(I.subscheme, U)) ^ b.factorial ≤ ⊥
    rw [Ideal.bot_pow (Nat.factorial_ne_zero b)]

theorem exists_boundary_integral_sequence_of_zero_coefficient
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hJ : J ≠ ⊥) (n : ℕ)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f H D)
    (hH : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
    (hzero : CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι = ⊥) :
    ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J, T.integralCenters ∧ T.boundaryCompatible β D := by
  let : Smooth (H.subschemeι ≫ f) := A.center_smooth
  have hp := (ZeroCenter.Construction.smoothCoefficientIdealSheaf_eq_bot_iff f J H (n + 1) (Nat.succ_pos n)).mp hzero
  have hd := (Global.SmoothCenterCriterion.Construction.smooth_global_center_order_iff_differentialIdeal f H J n).mp hp
  have he : H = Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n := le_antisymm hH hd
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).subscheme :=
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  exact IntrinsicBoundaryIntegralSequence.Construction.exists_boundary_integral_sequence_of_intrinsic_atlas f J hJ n D (he ▸ A)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Permissibility.Construction
