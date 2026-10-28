import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Differential Ideal Sheaf -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf.Construction

noncomputable section

/-! The actual intrinsic differential ideal sheaf on a smooth complex scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The coefficient algebra on an affine open is supplied by the original
complex structure morphism. -/
abbrev affineComplexAlgebra (U : X.affineOpens) : Algebra ℂ Γ(X, U) :=
  (Affine.ComplexNaturality.Construction.affineComplexScalars f U).toAlgebra

/-- Smoothness of each actual affine chart over the original complex base. -/
theorem affineComplexAlgebra_smooth [Smooth f] (U : X.affineOpens) :
    letI := affineComplexAlgebra f U
    Algebra.Smooth ℂ Γ(X, U) := by
  let : Algebra ℂ Γ(X, U) := affineComplexAlgebra f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have h : Smooth (Spec.map (CommRingCat.ofHom (Affine.ComplexNaturality.Construction.affineComplexScalars f U))) := by
    rw [Affine.ComplexNaturality.Construction.affineComplexScalars_spec]
    infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h

variable [Smooth f]

/-- The intrinsic differential filtration as a native ideal sheaf. Its
restriction law follows from smooth étale compatibility on actual principal opens. -/
def smoothDifferentialIdealSheaf (I : X.IdealSheafData) (n : ℕ) : X.IdealSheafData where
  ideal U := letI := affineComplexAlgebra f U
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (I.ideal U) n
  map_ideal_basicOpen U s := by
    let V := X.affineBasicOpen s
    have hVU : V ≤ U := X.basicOpen_le s
    let : Algebra ℂ Γ(X, U) := affineComplexAlgebra f U
    let : Algebra ℂ Γ(X, V) := affineComplexAlgebra f V
    let : Algebra Γ(X, U) Γ(X, V) := (Blowup.Functor.Construction.affineRestriction hVU).toAlgebra
    let : IsScalarTower ℂ Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq' (Affine.ComplexNaturality.Construction.affineComplexScalars_restrict f hVU).symm
    let : IsLocalization.Away s Γ(X, V) :=
      U.2.isLocalization_of_eq_basicOpen s (homOfLE hVU) rfl
    let : Algebra.FormallyEtale Γ(X, U) Γ(X, V) :=
      Algebra.FormallyEtale.of_isLocalization (Submonoid.powers s)
    let : Algebra.Smooth ℂ Γ(X, U) := affineComplexAlgebra_smooth f U
    have he := DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange ℂ (S := Γ(X, V)) (I.ideal U) n
    exact he.trans (congrArg (fun J : Ideal Γ(X, V) => Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n)
      (I.map_ideal hVU))

/-- On every affine open the sheaf is exactly the algebraic differential
ideal, using the complex scalars induced by the original structure map. -/
theorem smoothDifferentialIdealSheaf_ideal (I : X.IdealSheafData) (n : ℕ) (U : X.affineOpens) :
    letI := affineComplexAlgebra f U
    (smoothDifferentialIdealSheaf f I n).ideal U =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (I.ideal U) n := rfl

theorem smoothDifferentialIdealSheaf_zero (I : X.IdealSheafData) :
    smoothDifferentialIdealSheaf f I 0 = I := by
  ext U
  rfl

theorem smoothDifferentialIdealSheaf_mono {I J : X.IdealSheafData} (h : I ≤ J) (n : ℕ) :
    smoothDifferentialIdealSheaf f I n ≤ smoothDifferentialIdealSheaf f J n := by
  intro U
  let : Algebra ℂ Γ(X, U) := affineComplexAlgebra f U
  exact Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono ℂ n (h U)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf.Construction
