import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Auxiliary
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialProducts
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ZeroCenter

/-! # Carrier Auxiliary Coefficients -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CarrierAuxiliaryCoefficients.Construction

noncomputable section

/-! Adding a carrier's control power leaves its intrinsic coefficient ideal unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothDifferentialIdealSheaf_sup
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J K : X.IdealSheafData) (n : ℕ) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (J ⊔ K) n =
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n ⊔ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f K n := by
  apply Scheme.IdealSheafData.ext
  funext U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  exact Relative.DifferentialProducts.Construction.iteratedRelativeDifferentialIdeal_sup ℂ (J.ideal U) (K.ideal U) n

theorem carrier_power_differential_comap_eq_bot
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (H : X.IdealSheafData)
    (b j : ℕ) (hj : j < b) : (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (H ^ b) j).comap H.subschemeι = ⊥ := by
  have hd : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (H ^ b) j ≤ H := by
    intro U
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ ((H.ideal U) ^ b) j ≤ H.ideal U
    have hp : (H.ideal U) ^ b ≤ (H.ideal U) ^ (1 + j) := Ideal.pow_le_pow_right (by omega)
    have h := (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary ℂ ((H.ideal U) ^ b) j).trans
      (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow (H.ideal U) ((H.ideal U) ^ b) 1 j hp)
    simpa only [pow_one] using h
  have h := Scheme.IdealSheafData.comap_mono H.subschemeι hd
  change (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (H ^ b) j).comap H.subschemeι ≤ H.comap H.subschemeι at h
  have hH : H.comap H.subschemeι = ⊥ := (GlobalCoefficient.ZeroCenter.Construction.idealSheaf_comap_subscheme_eq_bot_iff H H).mpr le_rfl
  rw [hH] at h
  exact le_bot_iff.mp h

theorem smoothCoefficientIdealSheaf_carrier_auxiliary
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (b : ℕ) :
    GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H b) b H.subschemeι =
      GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι := by
  unfold GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal
  apply congrArg iSup
  funext j
  rw [smoothDifferentialIdealSheaf_sup, Scheme.IdealSheafData.comap_sup,
    carrier_power_differential_comap_eq_bot f H b j.val j.isLt, sup_bot_eq]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CarrierAuxiliaryCoefficients.Construction
