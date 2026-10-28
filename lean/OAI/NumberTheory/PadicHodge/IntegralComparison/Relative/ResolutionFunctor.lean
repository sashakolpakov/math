import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComposition

/-! # Resolution Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor

noncomputable section

/-!
# IntegralComparison: the original relative crystalline complex is a functor of its diagram over the base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (Q : C ⥤ BigCrystallineSite.Object p B J δ f)

def functor : (Over Q)ᵒᵖ ⥤ CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℕ where
  obj U := RelativeCrystalline.ModuleComplex.complex U.unop.left Q U.unop.hom
  map α := DiagramComplexMap.map _ _ Q _ _ α.unop.left (Over.w α.unop)
  map_id U := DiagramComposition.complex_id U.unop.left Q U.unop.hom
  map_comp α β := DiagramComposition.complex_comp _ _ _ Q _ _ _
    β.unop.left α.unop.left (Over.w β.unop) (Over.w α.unop)

def overIso {H K : C ⥤ BigCrystallineSite.Object p B J δ f} (π : H ⟶ Q) (ρ : K ⟶ Q)
    (e : H ≅ K) (he : e.hom ≫ ρ = π) : (Over.mk π) ≅ (Over.mk ρ) :=
  Over.isoMk e he

def imageIso {H K : C ⥤ BigCrystallineSite.Object p B J δ f} (π : H ⟶ Q) (ρ : K ⟶ Q)
    (e : H ≅ K) (he : e.hom ≫ ρ = π) :
    (functor Q).obj (op (Over.mk ρ)) ≅ (functor Q).obj (op (Over.mk π)) :=
  (functor Q).mapIso (overIso Q π ρ e he).op

def diagramIso {H K : C ⥤ BigCrystallineSite.Object p B J δ f} (π : H ⟶ Q) (ρ : K ⟶ Q)
    (e : H ≅ K) (he : e.hom ≫ ρ = π) :
    RelativeCrystalline.ModuleComplex.complex K Q ρ ≅ RelativeCrystalline.ModuleComplex.complex H Q π :=
  imageIso Q π ρ e he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor
