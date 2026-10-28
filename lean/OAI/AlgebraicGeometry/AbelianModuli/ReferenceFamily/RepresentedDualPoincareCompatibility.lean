import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PoincareComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport

/-! # Represented Dual Poincare Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedDualPoincareCompatibility

noncomputable section

/-! Representing dual comparisons preserve Poincare classes along
an original-family group isomorphism. Only the original target family
needs a projective presentation; no group comparison of the dual is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ} {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem representedDualComparison_poincare (D : HilbertConstruction.Dual.Data.DualAbelianData A) (E : HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (P : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation B.scheme) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (((D.familyTransport e).uniqueUnderlyingIso E).hom ⊗ₘ e.hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare := by
  let d : D.abelian.scheme ⟶ E.abelian.scheme := ((D.familyTransport e).uniqueUnderlyingIso E).hom
  let l := 𝟙 D.abelian.scheme ⊗ₘ e.hom
  have h : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 B.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (D.familyTransport e).poincare := by
    rw [tensorHom_id]
    change HilbertConstruction.Line.Bundles.LineBundle.classOf (E.poincareAt d) = _
    exact Quotient.sound ⟨((D.familyTransport e).uniqueUnderlyingIso_poincare_iso E P).some.symm⟩
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 B.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.inv).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) at h
  have hl : l ≫ (d ⊗ₘ 𝟙 B.scheme) = d ⊗ₘ e.hom := by
    simpa only [l, id_tensorHom, tensorHom_id] using (tensorHom_def' d e.hom).symm
  have hr : l ≫ (𝟙 D.abelian.scheme ⊗ₘ e.inv) = 𝟙 _ := by simp [l]
  have H := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass l.left) h
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, hl, hr, Over.id_left, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedDualPoincareCompatibility
