import OAI.NumberTheory.PadicHodge.IntegralComparison.RegularSequenceKoszul
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology
import Mathlib.Algebra.Homology.Linear

/-! # Dual Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualFunctor

noncomputable section

/-! The genuine coefficient dual carries the scalar Koszul construction to
scalar mapping cones in the opposite module category. This uses additivity,
and does not assume that the coefficient ring is injective. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite

universe u
variable (R : Type u) [CommRing R]

private def oppositeHomAddEquiv (X Y : (ModuleCat.{u} R)ᵒᵖ) :
    (X ⟶ Y) ≃+ (Y.unop ⟶ X.unop) where
  toEquiv := CategoryTheory.opEquiv X Y
  map_add' _ _ := rfl

instance oppositeLinear : CategoryTheory.Linear R (ModuleCat.{u} R)ᵒᵖ where
  homModule X Y := (oppositeHomAddEquiv R X Y).module R
  smul_comp X Y Z r f g := by
    apply Quiver.Hom.unop_inj
    change g.unop ≫ (r • f.unop) = r • (g.unop ≫ f.unop)
    simp only [CategoryTheory.Linear.comp_smul]
  comp_smul X Y Z f r g := by
    apply Quiver.Hom.unop_inj
    change (r • g.unop) ≫ f.unop = r • (g.unop ≫ f.unop)
    simp only [CategoryTheory.Linear.smul_comp]

abbrev functor : ModuleCat.{u} R ⥤ (ModuleCat.{u} R)ᵒᵖ :=
  (ExactModuleDualFunctor.functor R).rightOp

instance : Functor.Linear R (functor R) where
  map_smul := by
    intro X Y f r
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    exact φ.map_smul r (f.hom x)

abbrev complex (K : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((functor R).mapHomologicalComplex (.up ℤ)).obj K

theorem scalar_eq_smul_id (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : R) :
    RegularElementKoszul.scalar K r = r • 𝟙 K := by
  rfl

theorem map_scalar (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : R) :
    ((functor R).mapHomologicalComplex (.up ℤ)).map (RegularElementKoszul.scalar K r) =
      r • 𝟙 (complex R K) := by
  rw [scalar_eq_smul_id, Functor.map_smul, CategoryTheory.Functor.map_id]

def coneIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : R) :
    complex R (CochainComplex.mappingCone (RegularElementKoszul.scalar K r)) ≅
      CochainComplex.mappingCone (r • 𝟙 (complex R K)) :=
  HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso
    (RegularElementKoszul.scalar K r) (functor R) ≪≫
      eqToIso (by rw [map_scalar]; rfl)

def ordinaryDualIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    complex R K ≅ (DualComplexHomology.complex R K).op :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by intros; rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualFunctor
