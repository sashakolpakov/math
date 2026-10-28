import OAI.NumberTheory.PadicHodge.IntegralComparison.CoordinateSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality

/-! # Inverse Coordinate Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! Homology preserves the inverse-coordinate form of a commutative square. -/

open _root_.CategoryTheory

universe u v

theorem inverse {C : Type u} [Category.{v} C] {A A' B B' : C}
    (e : A ≅ A') (d : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ d.hom = e.hom ≫ g) : g ≫ d.inv = e.inv ≫ f := by
  have hf : f ≫ 𝟙 B = 𝟙 A ≫ f := (Category.comp_id f).trans (Category.id_comp f).symm
  simpa only [Category.comp_id] using CoordinateSquare.Comparison.conjugate e d f g (𝟙 A) (𝟙 B) f h hf

theorem homology {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B B' : CochainComplex C ℕ} (e : A ≅ A') (d : B ≅ B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : f ≫ d.hom = e.hom ≫ g) (i : ℕ) :
    HomologicalComplex.homologyMap g i ≫ HomologicalComplex.homologyMap d.inv i =
      HomologicalComplex.homologyMap e.inv i ≫ HomologicalComplex.homologyMap f i :=
  (HomologicalComplex.homologyMap_comp g d.inv i).symm.trans
    ((congrArg (fun a => HomologicalComplex.homologyMap a i) (inverse e d f g h)).trans
      (HomologicalComplex.homologyMap_comp e.inv f i))

end OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology
