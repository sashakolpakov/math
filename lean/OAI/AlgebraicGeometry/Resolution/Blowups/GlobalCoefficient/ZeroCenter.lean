import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents

/-! # Zero Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ZeroCenter.Construction

noncomputable section

/-! A zero global coefficient ideal characterizes permissibility of the whole smooth closed carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_pow_eq_bot {X : Scheme} [IsReduced X] (I : X.IdealSheafData) (n : ℕ) (hn : n ≠ 0) :
    I ^ n = ⊥ ↔ I = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff, Scheme.IdealSheafData.support_pow I n hn,
    Scheme.IdealSheafData.support_eq_top_iff]

theorem idealSheaf_comap_subscheme_eq_bot_iff {X : Scheme} (I H : X.IdealSheafData) :
    I.comap H.subschemeι = ⊥ ↔ I ≤ H := by
  constructor
  · intro h
    have he := (Scheme.IdealSheafData.map_gc H.subschemeι I ⊥).mp h.le
    change I ≤ (⊥ : H.subscheme.IdealSheafData).map H.subschemeι at he
    rwa [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at he
  · intro h
    apply le_bot_iff.mp
    apply (Scheme.IdealSheafData.map_gc H.subschemeι I ⊥).mpr
    change I ≤ (⊥ : H.subscheme.IdealSheafData).map H.subschemeι
    rwa [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

theorem smoothCoefficientIdealSheaf_eq_bot_iff
    {X : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J H : X.IdealSheafData) [Smooth (H.subschemeι ≫ f)] (b : ℕ) (hb : 0 < b) :
    CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι = ⊥ ↔ J ≤ H ^ b := by
  constructor
  · intro hzero
    let : IsReduced H.subscheme := Blowups.Smooth.CenterComponents.Construction.smooth_complex_scheme_isReduced (H.subschemeι ≫ f)
    let j : Fin b := ⟨b - 1, by omega⟩
    have hj : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val).comap H.subschemeι) ^ WeightedCoefficientIdeal.Construction.coefficientWeight b j ≤
        CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι :=
      le_iSup (fun r : Fin b => ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r.val).comap H.subschemeι) ^ WeightedCoefficientIdeal.Construction.coefficientWeight b r) j
    rw [hzero] at hj
    have hz := (idealSheaf_pow_eq_bot _ _ (Nat.ne_of_gt (WeightedCoefficientIdeal.Construction.coefficientWeight_pos b j))).mp (le_bot_iff.mp hj)
    have hd := (idealSheaf_comap_subscheme_eq_bot_iff _ H).mp hz
    have hJ := (Global.SmoothCenterCriterion.Construction.smooth_global_center_order_iff_differentialIdeal f H J (b - 1)).mpr hd
    simpa only [Nat.sub_add_cancel hb] using hJ
  · intro hJ
    have h := CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_le_of_order f H J b H.subschemeι hJ
    have hH : H.comap H.subschemeι = ⊥ := (idealSheaf_comap_subscheme_eq_bot_iff H H).mpr le_rfl
    rw [hH] at h
    apply le_bot_iff.mp (h.trans _)
    intro U
    change (⊥ : Ideal Γ(H.subscheme, U)) ^ b.factorial ≤ ⊥
    rw [Ideal.bot_pow (Nat.factorial_ne_zero b)]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ZeroCenter.Construction
