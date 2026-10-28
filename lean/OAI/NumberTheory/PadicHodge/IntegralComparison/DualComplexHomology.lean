import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactModuleDualFunctor
import Mathlib.Algebra.Homology.Opposite

/-! # Dual Complex Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology

noncomputable section

/-! Over an injective coefficient ring, the homology of the ordinary
dual complex is the ordinary dual of homology, naturally in the complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

theorem map_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B C' D' : C} (a : A ⟶ B) (b : B ⟶ D')
    (c : A ⟶ C') (d : C' ⟶ D') (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, h, F.map_comp]

theorem compose_squares {C : Type*} [Category* C] {A B D E G H : C}
    (f : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E) (c : A ⟶ G) (d : G ⟶ H)
    (g : H ⟶ E) (m : G ⟶ D) (h₁ : f ≫ a = c ≫ m) (h₂ : m ≫ b = d ≫ g) :
    f ≫ (a ≫ b) = (c ≫ d) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

variable (R : Type u) [CommRing R] {ι : Type v} {c : ComplexShape ι}

abbrev dual := ExactModuleDualFunctor.functor R

def complex (K : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (ModuleCat.{u} R) c.symm :=
  ((dual R).mapHomologicalComplex c.symm).obj K.op

def map {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) :
    complex R L ⟶ complex R K :=
  ((dual R).mapHomologicalComplex c.symm).map
    ((HomologicalComplex.opFunctor (ModuleCat.{u} R) c).map f.op)

variable [Module.Injective R R]

def homologyIso (K : HomologicalComplex (ModuleCat.{u} R) c) (i : ι) :
    (complex R K).homology i ≅ ModuleCat.of R (Module.Dual R (K.homology i)) :=
  (K.op.sc i).mapHomologyIso (dual R) ≪≫ (dual R).mapIso (K.homologyOp i)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem naturality {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap (DualComplexHomology.map R f) i ≫ (homologyIso R K i).hom =
      (homologyIso R L i).hom ≫ ModuleCat.ofHom (HomologicalComplex.homologyMap f i).hom.dualMap := by
  let fop := (HomologicalComplex.opFunctor (ModuleCat.{u} R) c).map f.op
  have h₁ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)ᵒᵖ c.symm i).map fop) (dual R)
  have h₂ := map_square (dual R) _ _ _ _ (HomologicalComplex.homologyOp_hom_naturality f i)
  change HomologicalComplex.homologyMap (DualComplexHomology.map R f) i ≫ ((K.op.sc i).mapHomologyIso (dual R)).hom =
    ((L.op.sc i).mapHomologyIso (dual R)).hom ≫ (dual R).map (HomologicalComplex.homologyMap fop i) at h₁
  exact compose_squares _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology
