import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PoincareComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DualComparison

/-! # Family Poincare Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Canonical dual comparisons along abelian-family isomorphisms preserve the actual Poincare line-bundle class, as required by HilbertConstruction's moduli isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}

theorem Dual.Data.DualAbelianData.uniqueUnderlyingIso_poincare_class (D E : Dual.Data.DualAbelianData A)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) :
    Line.Bundles.LineBundle.pullbackClass ((D.uniqueUnderlyingIso E).hom ⊗ₘ 𝟙 A.scheme).left
      (Line.Bundles.LineBundle.classOf E.poincare) = Line.Bundles.LineBundle.classOf D.poincare := by
  rw [tensorHom_id]
  change Line.Bundles.LineBundle.classOf (E.poincareAt (D.uniqueUnderlyingIso E).hom) = Line.Bundles.LineBundle.classOf D.poincare
  exact Quotient.sound ⟨(D.uniqueUnderlyingIso_poincare_iso E P).some.symm⟩

theorem Dual.Data.DualAbelianData.familyComparisonIso_poincare (D : Dual.Data.DualAbelianData A) (E : Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (P : Projective.ProjectivePresentations.ProjectivePresentation B.scheme) :
    Line.Bundles.LineBundle.pullbackClass ((D.familyComparisonIso E e).hom ⊗ₘ e.hom).left
      (Line.Bundles.LineBundle.classOf E.poincare) = Line.Bundles.LineBundle.classOf D.poincare := by
  let d := (D.familyComparisonIso E e).hom
  let l := 𝟙 D.abelian.scheme ⊗ₘ e.hom
  have h := (D.familyTransport e).uniqueUnderlyingIso_poincare_class E P
  change Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 B.scheme).left (Line.Bundles.LineBundle.classOf E.poincare) =
    Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.inv).left (Line.Bundles.LineBundle.classOf D.poincare) at h
  have hl : l ≫ (d ⊗ₘ 𝟙 B.scheme) = d ⊗ₘ e.hom := by
    simpa only [l, id_tensorHom, tensorHom_id] using (tensorHom_def' d e.hom).symm
  have hr : l ≫ (𝟙 D.abelian.scheme ⊗ₘ e.inv) = 𝟙 _ := by simp [l]
  have H := congrArg (Line.Bundles.LineBundle.pullbackClass l.left) h
  rw [← Line.Bundles.LineBundle.pullbackClass_comp, ← Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, hl, hr, Over.id_left, Line.Bundles.LineBundle.pullbackClass_id] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
