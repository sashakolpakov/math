import OAI.RepresentationTheory.Theta.Geometric.Geometry

/-! # Action -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

open scoped TensorProduct

instance Intrinsic.Action.oneFormsRationalModule (X : CategoryTheory.Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℚ (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X) :=
  Module.compHom _ (algebraMap ℚ ℂ)

instance Intrinsic.Action.oneFormsRationalTower (X : CategoryTheory.Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsScalarTower ℚ ℂ (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X) :=
  IsScalarTower.of_compHom ℚ ℂ _

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def Intrinsic.Action.activeHeckeMap (e : SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] SphericalGU.Spherical.activeAlgebra q v) :
    SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] SphericalGU.Spherical.FullHecke q s :=
  (SphericalGU.Spherical.activeAlgebra q v).val.comp e.toAlgHom

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.activeH1Complex (A : TateComparison.Action D.pel)
    (e : SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished) :
    ℂ ⊗[ℚ] SphericalGU.Spherical.SL3Hecke q →ₗ[ℂ] Module.End ℂ (ℂ ⊗[ℚ] D.pel.H1) :=
  Complexify.complexifyOperator (A := SphericalGU.Spherical.SL3Hecke q) (V := ℂ ⊗[ℚ] D.pel.H1)
    ((LinearMap.baseChangeHom (R := ℚ) (M := D.pel.H1) (N := D.pel.H1) ℂ).comp
    (A.cohomologyAction.toLinearMap.comp
      (Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e).toLinearMap))

def Data.ActiveHeckeThetaData.activeFormsComplex
    (rho : SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (e : SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished) :
    ℂ ⊗[ℚ] SphericalGU.Spherical.SL3Hecke q →ₗ[ℂ] Module.End ℂ D.pel.OneFormsA :=
  Complexify.complexifyOperator (A := SphericalGU.Spherical.SL3Hecke q) (V := D.pel.OneFormsA)
    (rho.comp (Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e).toLinearMap)

def Data.ActiveHeckeThetaData.sphericalWeilComplex : ℂ ⊗[ℚ] SphericalGU.Spherical.SL3Hecke q →ₗ[ℂ]
    Module.End ℂ D.sphericalInputs :=
  Complexify.complexifyOperator (A := SphericalGU.Spherical.SL3Hecke q) (V := D.sphericalInputs) D.sphericalWeilLinear

def Data.ActiveHeckeThetaData.ballH1ComplexProjector (j : Fin D.pel.componentCount) :
    Module.End ℂ (ℂ ⊗[ℚ] D.pel.H1) := (D.ballH1Projector j).baseChange ℂ

end

end OAI.RepresentationTheory.Theta.Geometric
