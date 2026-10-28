import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor

/-! # Resolution Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionAugmentation

noncomputable section

/-!
# IntegralComparison: the structure-presheaf augmentation is natural in the relative crystalline diagram
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (Q : C ⥤ BigCrystallineSite.Object p B J δ f)

def augmentation : (Functor.const (Over Q)ᵒᵖ).obj
    ((CochainComplex.single₀ _).obj (RelativeCrystalline.ModuleComplex.ambientPresheaf Q)) ⟶
      ResolutionFunctor.functor Q where
  app U := RelativeCrystalline.ModuleComplex.augmentation U.unop.left Q U.unop.hom
  naturality U V α := (Category.id_comp _).trans
    (DiagramComplexMap.augmentation V.unop.left U.unop.left Q V.unop.hom U.unop.hom
      α.unop.left (Over.w α.unop)).symm

theorem diagramIso {H K : C ⥤ BigCrystallineSite.Object p B J δ f} (π : H ⟶ Q) (ρ : K ⟶ Q)
    (e : H ≅ K) (he : e.hom ≫ ρ = π) :
    RelativeCrystalline.ModuleComplex.augmentation K Q ρ ≫
      (ResolutionFunctor.diagramIso Q π ρ e he).hom =
        RelativeCrystalline.ModuleComplex.augmentation H Q π :=
  ((augmentation Q).naturality (ResolutionFunctor.overIso Q π ρ e he).hom.op).symm.trans
    (Category.id_comp _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionAugmentation
