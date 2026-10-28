import OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeExtensionNormalization

/-! # Nonnegative Extension Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeExtensionNaturality.Complex

noncomputable section

/-! The canonical identification of the two integer-extension conventions is natural in actual cochain morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.Complex

variable {C : Type*} [Category* C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {e e' : c.Embedding c'} {K L : HomologicalComplex C c}

theorem extensionIsoOfEq_naturality (h : e = e') (φ : K ⟶ L) :
    (NonnegativeExtensionNormalization.Complex.extensionIsoOfEq h K).hom ≫ HomologicalComplex.extendMap φ e' =
      HomologicalComplex.extendMap φ e ≫ (NonnegativeExtensionNormalization.Complex.extensionIsoOfEq h L).hom := by
  subst e'
  simp only [NonnegativeExtensionNormalization.Complex.extensionIsoOfEq, eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]

theorem nonnegativeExtensionIso_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso K).hom ≫ HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat =
      HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntGE 0) ≫ (NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso L).hom :=
  extensionIsoOfEq_naturality NonnegativeExtensionNormalization.Complex.embeddingUpIntGE_zero_eq φ

end

end OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeExtensionNaturality.Complex
