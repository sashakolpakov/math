import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechSectionCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechUnitNaturality

/-! # Cech Functor Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechFunctorCoordinates.LargeZariskiCechFunctorCoordinates

noncomputable section

/-! # Functorial intersection coordinates for global Čech cochains -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenInjectives.LargeZariskiOpenInjectives.Modules R
local notation "Psh" => OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf.MixedCechPresheaf.Presheaves R X
local notation "J" => Opens.grothendieckTopology X
local notation "Ev" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechSectionCoordinates.LargeZariskiCechSectionCoordinates.evaluation R X

local instance coefficientLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def coefficientsIso : MixedCech.Functor.MixedCechFunctor.coefficients R X ⋙
    (Functor.whiskeringRight X.Opensᵒᵖ Psh V).obj Ev ≅ 𝟭 Psh :=
  NatIso.ofComponents (CechSectionCoordinates.LargeZariskiCechSectionCoordinates.coefficientsIso R X) (by
    intro P Q f
    apply NatTrans.ext
    funext W
    exact (f.naturality (eqToHom (congrArg op (top_inf_eq (a := W.unop))))).symm)

variable {ι : Type u} (U : ι → X.Opens)

def presheafIso : MixedCech.Functor.MixedCechFunctor.functor R X U ⋙ (Ev).mapHomologicalComplex (ComplexShape.up ℕ) ≅
    cechComplexFunctor U :=
  Functor.associator (MixedCech.Functor.MixedCechFunctor.coefficients R X) (cechComplexFunctor U)
    ((Ev).mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫
      Functor.isoWhiskerLeft (MixedCech.Functor.MixedCechFunctor.coefficients R X)
        (Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.iso Ev (FormalCoproduct.mk ι U).cech) ≪≫
          (Functor.associator (MixedCech.Functor.MixedCechFunctor.coefficients R X)
            ((Functor.whiskeringRight X.Opensᵒᵖ Psh V).obj Ev) (cechComplexFunctor U)).symm ≪≫
              Functor.isoWhiskerRight (coefficientsIso R X) (cechComplexFunctor U) ≪≫
                Functor.leftUnitor (cechComplexFunctor U)

def sheafIso : MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U ⋙
    (Sheaf.Γ J V).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      sheafToPresheaf J V ⋙ cechComplexFunctor U :=
  Functor.isoWhiskerLeft (MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U)
    (NatIso.mapHomologicalComplex (Sheaf.ΓNatIsoSheafSections J V
      (isTerminalTop : IsTerminal (⊤ : X.Opens))) (ComplexShape.up ℕ)) ≪≫
    (Functor.associator (MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U)
      ((sheafToPresheaf J V).mapHomologicalComplex (ComplexShape.up ℕ))
      ((Ev).mapHomologicalComplex (ComplexShape.up ℕ))).symm ≪≫
        Functor.isoWhiskerRight (CechUnitNaturality.LargeZariskiCechUnitNaturality.iso R X U).symm
          ((Ev).mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫
            Functor.associator (sheafToPresheaf J V) (MixedCech.Functor.MixedCechFunctor.functor R X U)
              ((Ev).mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫
                Functor.isoWhiskerLeft (sheafToPresheaf J V) (presheafIso R X U)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechFunctorCoordinates.LargeZariskiCechFunctorCoordinates
