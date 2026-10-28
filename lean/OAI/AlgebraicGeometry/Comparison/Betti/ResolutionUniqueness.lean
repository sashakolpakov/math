import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! # Resolution Uniqueness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ResolutionUniqueness

noncomputable section

/-!
# Uniqueness of normalized resolution comparisons

Two maps from a proved resolution into a complex of injectives that agree
on the original augmentation are homotopic. Consequently every additive
functor, including actual open sections, gives the same cohomology map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]
  {Z : C} (R : ResolutionExactImage.Data Z) (L : CochainComplex C ℕ) [∀ n, Injective (L.X n)]
  (f g : R.complex ⟶ L)
  (h : ResolutionExactImage.cochainAugmentation R ≫ f = ResolutionExactImage.cochainAugmentation R ≫ g)

include h

def comparisonHomotopy : Homotopy f g := by
  letI := HasDerivedCategory.standard C
  let E := ComplexShape.embeddingUpNat.extendFunctor C
  let a := E.map (ResolutionExactImage.cochainAugmentation R)
  let f' : R.complex.extend ComplexShape.embeddingUpNat ⟶ L.extend ComplexShape.embeddingUpNat := E.map f
  let g' : R.complex.extend ComplexShape.embeddingUpNat ⟶ L.extend ComplexShape.embeddingUpNat := E.map g
  have ha : QuasiIso a :=
    (HomologicalComplex.quasiIso_extendMap_iff (ResolutionExactImage.cochainAugmentation R)
      ComplexShape.embeddingUpNat).mpr inferInstance
  have hi : IsIso (DerivedCategory.Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C a).mpr ha
  have hQ : DerivedCategory.Q.map f' = DerivedCategory.Q.map g' := by
    apply (cancel_epi (DerivedCategory.Q.map a)).mp
    have he : a ≫ f' = a ≫ g' := (E.map_comp (ResolutionExactImage.cochainAugmentation R) f).symm.trans
      ((E.congr_map h).trans (E.map_comp (ResolutionExactImage.cochainAugmentation R) g))
    exact (DerivedCategory.Q.map_comp a f').symm.trans
      ((DerivedCategory.Q.congr_map he).trans (DerivedCategory.Q.map_comp a g'))
  have hq : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f' =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g' := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective _
      (L.extend ComplexShape.embeddingUpNat)).injective
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app
      (L.extend ComplexShape.embeddingUpNat))).mp
    rw [DerivedCategory.quotientCompQhIso_hom_naturality,
      DerivedCategory.quotientCompQhIso_hom_naturality, hQ]
  exact (HomotopyCategory.homotopyOfEq f' g' hq).ofExtend

theorem comparison_homologyMap_eq {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map f) n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) n :=
  (F.mapHomotopy (comparisonHomotopy R L f g h)).homologyMap_eq n

end

end OAI.AlgebraicGeometry.Comparison.Betti.ResolutionUniqueness
