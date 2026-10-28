import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamSecondFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientCechFiniteness

/-! # Coefficient Second Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientSecondFiniteness

noncomputable section

/-! Finiteness of actual second-stage de Rham Cech cohomology with the original crystalline coefficients. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientComplex.coefficients p k
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamCechUnit.bicomplex k X
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientCechFiniteness.bicomplex p k X

local instance coefficientLimits : HasLimitsOfSize.{u, u}
    (ModuleCat.{u + 2} (ExactRestriction.Coeff (B := WittVector p k))) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}

local instance coefficientProducts : HasProducts.{u}
    (ModuleCat.{u + 2} (ExactRestriction.Coeff (B := WittVector p k))) :=
  fun I => (coefficientLimits p k).has_limits_of_shape (Discrete I)

local instance exactLimits : PreservesFiniteLimits G :=
  Functor.preservesFiniteLimits_of_preservesHomology G

local instance exactColimits : PreservesFiniteColimits G :=
  Functor.preservesFiniteColimits_of_preservesHomology G

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K ≅ L :=
  CechCoefficient.Total.bicomplexIso G (SmoothProper.DeRhamCechUnit.nerve k X)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X)

def complexIso (n : ℕ) : IntegralComparison.Module.TotalSecondClasses.horizontal (L).flip n ≅
    ((G).mapHomologicalComplex (.up ℕ)).obj (SmoothProper.DeRhamHomologyCech.complex k X n) :=
  BicomplexHomology.iso L n ≪≫
    HomologicalComplex.homologyMapIso (bicomplexIso p k X).symm n ≪≫
      ((K).sc n).mapHomologyIso ((G).mapHomologicalComplex (.up ℕ)) ≪≫
        ((G).mapHomologicalComplex (.up ℕ)).mapIso
          (Cech.PresheafExactness.homologyIso k (SmoothProper.DeRhamCechUnit.nerve k X)
            (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X) n)

def homologyIso (n q : ℕ) : (IntegralComparison.Module.TotalSecondClasses.horizontal (L).flip n).homology q ≅
    (G).obj ((SmoothProper.DeRhamHomologyCech.complex k X n).homology q) :=
  HomologicalComplex.homologyMapIso (complexIso p k X n) q ≪≫
    ((SmoothProper.DeRhamHomologyCech.complex k X n).sc q).mapHomologyIso G

omit [CharP k p] in
theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n q : ℕ) :
    Module.Finite (ExactRestriction.Coeff (B := WittVector p k))
      ((IntegralComparison.Module.TotalSecondClasses.horizontal (L).flip n).homology q) := by
  let : Module.Finite k ((SmoothProper.DeRhamHomologyCech.complex k X n).homology q) :=
    SmoothProper.DeRhamHomologyCech.finite k X hprojective n q
  let : Module.Finite (ExactRestriction.Coeff (B := WittVector p k))
      ((G).obj ((SmoothProper.DeRhamHomologyCech.complex k X n).homology q)) :=
    Global.DeRhamCoefficientFiniteness.finite p k _
  exact Module.Finite.equiv (homologyIso p k X n q).symm.toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientSecondFiniteness
