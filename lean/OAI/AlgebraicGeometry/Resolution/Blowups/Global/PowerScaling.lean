import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledPowerScaling
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Power Scaling -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.PowerScaling.Construction

noncomputable section

/-! Exact positive power scaling on native ideal sheaves and their actual global blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

theorem smooth_global_center_ideal_power_root
    (I J : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)]
    (b e : ℕ) (he : 0 < e) (hJ : J ^ e ≤ I ^ (b * e)) : J ≤ I ^ b := by
  intro U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let : Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U) := SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f I U
  exact Blowups.Smooth.CenterPowerRoot.Construction.smooth_center_ideal_power_root ℂ (I.ideal U) (J.ideal U) b e he (hJ U)

theorem smooth_global_terminal_power_iff (J : X.IdealSheafData)
    (b e : ℕ) (hb : 0 < b) (he : 0 < e) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (J ^ e) (b * e - 1) = ⊤ ↔
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1) = ⊤ := by
  constructor
  · intro h
    apply Scheme.IdealSheafData.ext
    funext U
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
    have hu := congrArg (fun L : X.IdealSheafData => L.ideal U) h
    exact (ControlledPowerScaling.Construction.smooth_relative_terminal_power_iff ℂ (J.ideal U) b e hb he).mp hu
  · intro h
    apply Scheme.IdealSheafData.ext
    funext U
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
    have hu := congrArg (fun L : X.IdealSheafData => L.ideal U) h
    exact (ControlledPowerScaling.Construction.smooth_relative_terminal_power_iff ℂ (J.ideal U) b e hb he).mpr hu

theorem globalBlowupControlledIdeal_pow_on_chart [IsIntegral X] [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b e : ℕ) (hp : J ≤ I ^ b)
    (U : X.affineOpens) (a : I.ideal U) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (J ^ e) hI (b * e)).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) =
      ((GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) ^ e).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) := by
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, IdealSheaf.ColonRestriction.Construction.idealSheaf_comap_pow_open,
    GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, ← Affine.QuotientKernel.Construction.affineQuotientKernel_pow]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel (ControlledPowerScaling.Construction.blowupControlledTransform_pow (I.ideal U)
    (J.ideal U) a b e (hp U))

theorem globalBlowupControlledIdeal_pow [IsIntegral X] [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b e : ℕ) (hp : J ≤ I ^ b) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (J ^ e) hI (b * e) =
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) ^ e := by
  exact IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (GlobalControlled.Chart.Construction.globalBlowupReesAffineCover I hI).openCover
    (fun p => globalBlowupControlledIdeal_pow_on_chart I J hI b e hp p.1 p.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.PowerScaling.Construction
