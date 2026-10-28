import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits

/-! # Zariski Cech Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechBicomplex

noncomputable section

/-!
# IntegralComparison: the functorial Čech bicomplex of an actual Zariski sheaf complex
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens)
  (A : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) ℕ)

def bicomplex : HomologicalComplex₂ (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{u + 1} R)) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U).mapHomologicalComplex (ComplexShape.up ℕ)).obj A

def singleBicomplex : HomologicalComplex₂ (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{u + 1} R)) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((CochainComplex.single₀ _).mapHomologicalComplex (ComplexShape.up ℕ)).obj A

def augmentation : singleBicomplex R X A ⟶ bicomplex R X U A :=
  ((AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor.MixedCechFunctor.sheafAugmentation R X U).mapHomologicalComplex (ComplexShape.up ℕ)).app A

def component (q : ℕ) : A.X q ⟶ ((bicomplex R X U A).X q).X 0 :=
  ((augmentation R X U A).f q).f 0

theorem vertical (q r : ℕ) (_h : (ComplexShape.up ℕ).Rel q r) :
    component R X U A q ≫ ((bicomplex R X U A).d q r).f 0 = A.d q r ≫ component R X U A r :=
  congrArg (fun f => f.f 0) ((augmentation R X U A).comm q r)

theorem horizontal (q : ℕ) : component R X U A q ≫ ((bicomplex R X U A).X q).d 0 1 = 0 :=
  ((CochainComplex.fromSingle₀Equiv _ _) ((augmentation R X U A).f q)).property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechBicomplex
