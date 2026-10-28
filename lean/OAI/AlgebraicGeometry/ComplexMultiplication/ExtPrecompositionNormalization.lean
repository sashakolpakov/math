import OAI.AlgebraicGeometry.ComplexMultiplication.ExtSmallComparison
import OAI.CategoryTheory.Sites.SheafCohomologyPair

/-! # Ext Precomposition Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ExtPrecompositionNormalization

noncomputable section

/-! # The actual Ext precomposition map as a derived morphism -/

open _root_.CategoryTheory Abelian

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt.{w} C]

theorem extPrecomposition_normalization {A B D F : C} (e : A ≅ B) (f : B ⟶ D)
    (n : ℕ) (b : Ext D F n) :
    Ext.homAddEquiv ((Ext.mk₀ e.hom).precomp F (zero_add n)
      ((Ext.mk₀ f).precomp F (zero_add n) b)) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map e.hom) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map f) ≫
          Ext.homAddEquiv b := by
  change Ext.hom ((Ext.mk₀ e.hom).comp ((Ext.mk₀ f).comp b (zero_add n))
    (zero_add n)) = _
  rw [Ext.comp_hom, Ext.comp_hom, Ext.mk₀_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ExtPrecompositionNormalization
