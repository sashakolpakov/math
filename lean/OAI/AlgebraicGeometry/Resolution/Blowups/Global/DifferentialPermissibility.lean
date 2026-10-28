import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement

/-! # Differential Permissibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialPermissibility.Construction

noncomputable section

/-! Global permissible centers lie in the original differential order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

/-- Differentiation lowers a native ideal-sheaf power bound by the specified order. -/
theorem smoothDifferentialIdealSheaf_le_pow (I J : X.IdealSheafData) (n r : ℕ)
    (hperm : J ≤ I ^ (n + r)) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r ≤ I ^ n := by
  intro U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  exact (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary ℂ (J.ideal U) r).trans
    (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow (I.ideal U) (J.ideal U) n r (hperm U))

/-- Every center permissible at control `n + 1` is supported inside the
original global order locus detected by the `n`th differential ideal. -/
theorem permissible_center_le_differential_support (I J : X.IdealSheafData) (n : ℕ)
    (hperm : J ≤ I ^ (n + 1)) :
    I.support ≤ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support := by
  apply Scheme.IdealSheafData.support_antitone
  have h := smoothDifferentialIdealSheaf_le_pow f I J 1 n
    (by simpa only [Nat.add_comm] using hperm)
  simpa only [pow_one] using h

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The actual permissible blowup is an isomorphism on every open set
disjoint from the original differential order locus. -/
theorem globalBlowup_isIso_off_differential_support (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (n : ℕ) (hperm : J ≤ I ^ (n + 1)) (U : X.Opens)
    (hU : U ≤ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.compl) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ U) := by
  apply Blowup.Complement.Construction.globalBlowup_isIso_on_open I hI U
  intro x hx hcenter
  exact hU hx (permissible_center_le_differential_support f I J n hperm hcenter)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialPermissibility.Construction
