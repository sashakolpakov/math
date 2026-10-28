import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeComplex

/-! # Postcompose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Postcompose

noncomputable section

/-!
# IntegralComparison: geometric postcomposition preserves the original frame section map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (F : BigCrystallineSite.Object p B J δ f) (τ : H ⟶ (Functor.const C).obj F)

def sourceIso : ComplexMap.constantComplex (C := C) ((BigCrystallineSite.postcompose g hg).obj F) ≅
    ComplexMap.constantComplex (C := C) F := Iso.refl _

theorem complexes :
    ComplexMap.map (H ⋙ BigCrystallineSite.postcompose g hg) (Q ⋙ BigCrystallineSite.postcompose g hg)
      (Functor.whiskerRight π (BigCrystallineSite.postcompose g hg)) ((BigCrystallineSite.postcompose g hg).obj F)
        (Functor.whiskerRight τ (BigCrystallineSite.postcompose g hg)) ≫ (Relative.PostcomposeComplex.complexIso g hg H Q π).hom =
      (sourceIso (C := C) g hg F).hom ≫ ComplexMap.map H Q π F τ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Postcompose
