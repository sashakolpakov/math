import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction

/-! # Frame Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FrameRestriction

noncomputable section

/-!
# IntegralComparison: frame maps commute with restriction of the original crystalline indexing category
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w v' w'

variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (t : D ⥤ C)
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (F : BigCrystallineSite.Object p B J δ f) (τ : H ⟶ (Functor.const C).obj F)

def sourceIso :
    ((Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (ComplexMap.constantComplex (C := C) F) ≅
        ComplexMap.constantComplex (C := D) F := Iso.refl _

theorem complexes :
    ((Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ComplexMap.map H Q π F τ) ≫ (Relative.ComplexRestriction.complexIso t H Q π).hom =
        (sourceIso t F).hom ≫ ComplexMap.map (t ⋙ H) (t ⋙ Q)
          (Functor.whiskerLeft t π) F (Functor.whiskerLeft t τ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FrameRestriction
