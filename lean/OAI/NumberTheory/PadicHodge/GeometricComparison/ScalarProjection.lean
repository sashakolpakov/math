import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Scalar Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarProjection.ScalarProjectionSquare

noncomputable section

/-! Elementary coefficient and projection identities used to check the actual scalar pullback square. -/

open _root_.CategoryTheory Limits

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

theorem projection (F : C ⥤ D) {α : Type w} (X : α → C) (Y Z : α → D)
    [HasProduct X] [HasProductsOfShape α D]
    (b : ∀ i, F.obj (X i) ⟶ Y i) (e : ∀ i, Y i ≅ Z i) (t : α) :
    (piComparison F X ≫ Limits.Pi.map b ≫ (Pi.mapIso e).hom) ≫ Pi.π Z t =
      F.map (Pi.π X t) ≫ b t ≫ (e t).hom := by
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.map_π_assoc, piComparison_comp_π_assoc]

theorem square (F : C ⥤ D) {M N A B : C} {M' N' A' B' : D}
    (g : M ⟶ N) (h : M' ⟶ N') (sM : F.obj M ⟶ M') (sN : F.obj N ⟶ N')
    (pM : M ⟶ A) (pN : N ⟶ B) (pM' : M' ⟶ A') (pN' : N' ⟶ B')
    (a : A ⟶ B) (b : A' ⟶ B') (cM : F.obj A ⟶ A') (cN : F.obj B ⟶ B')
    (hg : g ≫ pN = pM ≫ a) (hh : h ≫ pN' = pM' ≫ b)
    (hsM : sM ≫ pM' = F.map pM ≫ cM) (hsN : sN ≫ pN' = F.map pN ≫ cN)
    (hc : F.map a ≫ cN = cM ≫ b) :
    (F.map g ≫ sN) ≫ pN' = (sM ≫ h) ≫ pN' := by
  rw [Category.assoc, hsN, ← Category.assoc, ← F.map_comp, hg, F.map_comp,
    Category.assoc, hc, ← Category.assoc, ← hsM, Category.assoc, ← hh, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarProjection.ScalarProjectionSquare
