import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Extended Section -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendedSection.ExtendedSectionHomology

noncomputable section

/-! The passage from ordinary nonnegative section cohomology to integer section cohomology is natural. -/

open _root_.CategoryTheory Limits

theorem inverse_square {C : Type*} [Category* C] {A B A' B' : C}
    (e : A ≅ A') (d : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ d.hom = e.hom ≫ g) : g ≫ d.inv = e.inv ≫ f := by
  rw [← cancel_epi e.hom, ← cancel_mono d.hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id] using h.symm

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

def iso (K : CochainComplex C ℕ) (n : ℕ) :
    (((F.mapHomologicalComplex (.up ℕ)).obj K).homology n) ≅
      (((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).homology (n : ℤ)) :=
  (((F.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) rfl).symm ≪≫
      (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
        (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat K).symm

theorem naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map f) n ≫ (iso F L n).hom =
      (iso F K n).hom ≫ HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat))
        (n : ℤ) := by
  let f' := (F.mapHomologicalComplex (.up ℕ)).map f
  let H := HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)
  have h₁ := inverse_square
    (((F.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl)
    (((F.mapHomologicalComplex (.up ℕ)).obj L).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl)
    _ _ (HomologicalComplex.extendHomologyIso_hom_naturality f' ComplexShape.embeddingUpNat rfl)
  have hi := inverse_square
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat K)
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat L) _ _
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso_naturality F ComplexShape.embeddingUpNat f)
  have h₂ := congrArg H.map hi
  simp only [CategoryTheory.Functor.map_comp] at h₂
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendedSection.ExtendedSectionHomology
