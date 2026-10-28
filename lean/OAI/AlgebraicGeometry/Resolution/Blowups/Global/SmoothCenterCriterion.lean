import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterDifferentialCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Smooth Center Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterCriterion.Construction

noncomputable section

/-! A smooth closed center is permissible precisely when it lies inside the intrinsic order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

theorem smooth_global_center_radical (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] :
    I.radical = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U) := SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f I U
  change (I.ideal U).radical = I.ideal U
  exact ((Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mpr (Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced ℂ)).radical

variable [Smooth f] [IsLocallyNoetherian X]

theorem smooth_global_center_order_iff_differentialIdeal
    (I J : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (n : ℕ) :
    J ≤ I ^ (n + 1) ↔ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n ≤ I := by
  constructor <;> intro h U
  all_goals
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : Algebra ℚ Γ(X, U) := ((algebraMap ℂ Γ(X, U)).comp (algebraMap ℚ ℂ)).toAlgebra
    let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    let : Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U) := SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f I U
  · exact (Blowups.Smooth.CenterDifferentialCriterion.Construction.smooth_center_order_iff_relative_differentialIdeal ℂ (I.ideal U) (J.ideal U) n).mp (h U)
  · exact (Blowups.Smooth.CenterDifferentialCriterion.Construction.smooth_center_order_iff_relative_differentialIdeal ℂ (I.ideal U) (J.ideal U) n).mpr (h U)

theorem smooth_global_center_permissible_iff_support
    (I J : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (n : ℕ) :
    J ≤ I ^ (n + 1) ↔ I.support ≤ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support := by
  rw [smooth_global_center_order_iff_differentialIdeal f I J n,
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    Scheme.IdealSheafData.vanishingIdeal_support, smooth_global_center_radical f I]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterCriterion.Construction
