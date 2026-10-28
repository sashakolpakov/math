import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizedIntervalTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationIdempotence

/-! # Homogenization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.Homogenization.Construction

noncomputable section

/-! Intrinsic homogenization as a native global ideal sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

def smoothHomogenizedIdealSheaf (J : X.IdealSheafData) (n : ℕ) : X.IdealSheafData :=
  ⨆ j : Fin (n + 1), Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val *
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) ^ j.val

theorem smoothHomogenizedIdealSheaf_ideal (J : X.IdealSheafData) (n : ℕ) (U : X.affineOpens) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    (smoothHomogenizedIdealSheaf f J n).ideal U = Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ (J.ideal U) n := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  simp only [smoothHomogenizedIdealSheaf, Scheme.IdealSheafData.ideal_iSup, iSup_apply,
    Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_pow, Pi.mul_apply, Pi.pow_apply,
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_ideal, Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal]

theorem le_smoothHomogenizedIdealSheaf (J : X.IdealSheafData) (n : ℕ) :
    J ≤ smoothHomogenizedIdealSheaf f J n := by
  intro U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  rw [smoothHomogenizedIdealSheaf_ideal]
  exact Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal ℂ (J.ideal U) n

theorem smoothHomogenizedIdealSheaf_permissible_iff (I J : X.IdealSheafData) (n : ℕ) :
    smoothHomogenizedIdealSheaf f J n ≤ I ^ (n + 1) ↔ J ≤ I ^ (n + 1) := by
  constructor
  · exact (le_smoothHomogenizedIdealSheaf f J n).trans
  · intro h U
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    change (smoothHomogenizedIdealSheaf f J n).ideal U ≤ I.ideal U ^ (n + 1)
    rw [smoothHomogenizedIdealSheaf_ideal]
    exact (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal_permissible_iff ℂ (I.ideal U) (J.ideal U) n).mpr (h U)

theorem smoothHomogenizedIdealSheaf_tangent (J : X.IdealSheafData) (n : ℕ) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (smoothHomogenizedIdealSheaf f J n) n =
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n := by
  apply Scheme.IdealSheafData.ext
  funext U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  rw [Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_ideal, smoothHomogenizedIdealSheaf_ideal,
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_ideal]
  exact HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent ℂ (J.ideal U) n

theorem smoothHomogenizedIdealSheaf_mono {J L : X.IdealSheafData} (h : J ≤ L) (n : ℕ) :
    smoothHomogenizedIdealSheaf f J n ≤ smoothHomogenizedIdealSheaf f L n := by
  intro U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  rw [smoothHomogenizedIdealSheaf_ideal, smoothHomogenizedIdealSheaf_ideal]
  exact HomogenizationIdempotence.Construction.relativeHomogenizedIdeal_mono ℂ (h U) n

theorem smoothHomogenizedIdealSheaf_idempotent (J : X.IdealSheafData) (n : ℕ) :
    smoothHomogenizedIdealSheaf f (smoothHomogenizedIdealSheaf f J n) n =
      smoothHomogenizedIdealSheaf f J n := by
  apply Scheme.IdealSheafData.ext
  funext U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  rw [smoothHomogenizedIdealSheaf_ideal, smoothHomogenizedIdealSheaf_ideal]
  exact HomogenizationIdempotence.Construction.relativeHomogenizedIdeal_idempotent ℂ (J.ideal U) n

theorem smoothHomogenizedIdealSheaf_interval_eq (J L : X.IdealSheafData) (n : ℕ)
    (hJL : J ≤ L) (hLH : L ≤ smoothHomogenizedIdealSheaf f J n) :
    smoothHomogenizedIdealSheaf f L n = smoothHomogenizedIdealSheaf f J n := by
  apply le_antisymm
  · have h := smoothHomogenizedIdealSheaf_mono f hLH n
    rwa [smoothHomogenizedIdealSheaf_idempotent] at h
  · exact smoothHomogenizedIdealSheaf_mono f hJL n

theorem smooth_homogenized_interval_tangent_eq (J L : X.IdealSheafData) (n : ℕ)
    (hJL : J ≤ L) (hLH : L ≤ smoothHomogenizedIdealSheaf f J n) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f L n = Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n := by
  apply le_antisymm
  · have h := Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_mono f hLH n
    rwa [smoothHomogenizedIdealSheaf_tangent] at h
  · exact Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_mono f hJL n

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.Homogenization.Construction
