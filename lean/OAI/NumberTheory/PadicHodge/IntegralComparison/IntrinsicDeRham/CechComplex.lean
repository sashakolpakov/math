import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Cech Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic

noncomputable section

/-! The Čech bicomplex and its total for the original sheafified
algebraic de Rham complex, with its coefficient module structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R)))
  {ι : Type u} (U : ι → X.left.Opens)

def presheaves : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R) ⥤
    X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)

instance presheaves_additive : (presheaves R X).Additive where
  map_add := rfl

def presheafComplex : CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  ((presheaves R X).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  CechCoefficient.Total.bicomplex (FormalCoproduct.mk ι U).cech (presheafComplex R X)

def total : CochainComplex (ModuleCat.{u} R) ℕ := (bicomplex R X U).total (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic
