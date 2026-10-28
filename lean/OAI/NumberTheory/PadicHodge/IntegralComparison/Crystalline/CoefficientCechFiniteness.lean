import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamCechUnit

/-! # Coefficient Cech Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientCechFiniteness

noncomputable section

/-! The actual global de Rham Čech complex with original crystalline coefficients has finite cohomology. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local instance coefficientLimits : HasLimitsOfSize.{u, u}
    (ModuleCat.{u + 2} (ExactRestriction.Coeff (B := WittVector p k))) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}

local instance coefficientProducts : HasProducts.{u}
    (ModuleCat.{u + 2} (ExactRestriction.Coeff (B := WittVector p k))) :=
  fun I => (coefficientLimits p k).has_limits_of_shape (Discrete I)

def bicomplex : HomologicalComplex₂
    (ModuleCat.{u + 2} (ExactRestriction.Coeff (B := WittVector p k))) (.up ℕ) (.up ℕ) :=
  @CechCoefficient.Total.bicomplex.{u, u, u, u + 3, u + 2}
    X.left.Opens inferInstance (ModuleCat.{u + 2} (ExactRestriction.Coeff (B := WittVector p k)))
    inferInstance inferInstance (coefficientProducts p k)
    (SmoothProper.DeRhamCechUnit.nerve k X)
    (Global.DeRhamCoefficientComplex.complex p k X)

def total : CochainComplex
    (ModuleCat.{u + 2} (ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  (bicomplex p k X).total (.up ℕ)

def iso :
    ((Global.DeRhamCoefficientComplex.coefficients p k).mapHomologicalComplex (.up ℕ)).obj
      (SmoothProper.DeRhamCechUnit.total k X) ≅ CoefficientCechFiniteness.total p k X :=
  CechCoefficient.Total.totalIso (Global.DeRhamCoefficientComplex.coefficients p k)
    (SmoothProper.DeRhamCechUnit.nerve k X) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X)

def homologyIso (n : ℕ) :
    (Global.DeRhamCoefficientComplex.coefficients p k).obj
      ((SmoothProper.DeRhamCechUnit.total k X).homology n) ≅ (CoefficientCechFiniteness.total p k X).homology n :=
  (((SmoothProper.DeRhamCechUnit.total k X).sc n).mapHomologyIso
    (Global.DeRhamCoefficientComplex.coefficients p k)).symm ≪≫
      HomologicalComplex.homologyMapIso (iso p k X) n

omit [CharP k p] in
theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n : ℕ) :
    Module.Finite (ExactRestriction.Coeff (B := WittVector p k)) ((CoefficientCechFiniteness.total p k X).homology n) := by
  let : Module.Finite k ((SmoothProper.DeRhamCechUnit.total k X).homology n) :=
    SmoothProper.DeRhamCechUnit.finite k X hprojective n
  let : Module.Finite (ExactRestriction.Coeff (B := WittVector p k))
      ((Global.DeRhamCoefficientComplex.coefficients p k).obj ((SmoothProper.DeRhamCechUnit.total k X).homology n)) :=
    Global.DeRhamCoefficientFiniteness.finite p k _
  exact Module.Finite.equiv (homologyIso p k X n).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientCechFiniteness
