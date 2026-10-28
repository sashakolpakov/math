import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientSecondFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechPresheafExactness

/-! # Cech Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechCover

noncomputable section

/-! Original coefficient Cech complexes on the actual Zariski cover and their finite de Rham second stage. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

local instance coefficientLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 2} R) :=
  fun I => (coefficientLimits p k).has_limits_of_shape (Discrete I)

abbrev nerve := (FormalCoproduct.mk (SmoothProper.EtaleCover.Index k X)
  (SmoothProper.DeRhamZariski.opens k X)).cech

def bicomplex (K : CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u + 2} R) (.up ℕ) (.up ℕ) :=
  @CechCoefficient.Total.bicomplex.{u, u, u, u + 3, u + 2}
    X.left.Opens inferInstance (ModuleCat.{u + 2} R) inferInstance inferInstance (coefficientProducts p k)
    (nerve k X) K

def deRhamHomologyComplex (n : ℕ) : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  (FormalCoproduct.cochainComplexFunctor (nerve k X)).obj
    ((Global.DeRhamCoefficientComplex.complex p k X).homology n)

def deRhamBicomplexIso : CoefficientCechFiniteness.bicomplex p k X ≅
    bicomplex p k X (Global.DeRhamCoefficientComplex.complex p k X) :=
  eqToIso (congrArg (fun U : SmoothProper.EtaleCover.Index k X → X.left.Opens =>
    @CechCoefficient.Total.bicomplex.{u, u, u, u + 3, u + 2}
      X.left.Opens inferInstance (ModuleCat.{u + 2} R) inferInstance inferInstance (coefficientProducts p k)
      (FormalCoproduct.mk (SmoothProper.EtaleCover.Index k X) U).cech
      (Global.DeRhamCoefficientComplex.complex p k X))
        (funext (SmoothProper.FrobeniusCharts.opens_eq k X)))

def deRhamHomologyIso (n : ℕ) :
    IntegralComparison.Module.TotalSecondClasses.horizontal (CoefficientCechFiniteness.bicomplex p k X).flip n ≅
      deRhamHomologyComplex p k X n :=
  BicomplexHomology.iso (CoefficientCechFiniteness.bicomplex p k X) n ≪≫
    HomologicalComplex.homologyMapIso (deRhamBicomplexIso p k X) n ≪≫
      CechPresheafExactness.homologyIso (WittVector p k) (nerve k X)
        (Global.DeRhamCoefficientComplex.complex p k X) n

omit [CharP k p] in
theorem deRhamHomology_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n q : ℕ) :
    Module.Finite R ((deRhamHomologyComplex p k X n).homology q) := by
  let : Module.Finite R
      ((IntegralComparison.Module.TotalSecondClasses.horizontal (CoefficientCechFiniteness.bicomplex p k X).flip n).homology q) :=
    CoefficientSecondFiniteness.finite p k X hprojective n q
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (deRhamHomologyIso p k X n) q).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechCover
