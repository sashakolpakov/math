import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedPolarizedPoincareComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DualComparison

/-! # Changed Polarized Poincare Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Canonical dual comparisons along group isomorphisms preserve the complete Poincare class on every base change of fixed polarized locally Noetherian families. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S T : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.baseChanged_uniqueDualIso_poincare_class
    (D E : Dual.Data.DualAbelianData (A.pullback f).abelian) :
    Line.Bundles.LineBundle.pullbackClass ((D.uniqueUnderlyingIso E).hom ⊗ₘ 𝟙 (A.pullback f).abelian.scheme).left
      (Line.Bundles.LineBundle.classOf E.poincare) = Line.Bundles.LineBundle.classOf D.poincare := by
  rw [tensorHom_id]
  change Line.Bundles.LineBundle.classOf (E.poincareAt (D.uniqueUnderlyingIso E).hom) = Line.Bundles.LineBundle.classOf D.poincare
  exact Quotient.sound ⟨(A.baseChanged_uniqueDualIso_poincare_iso f D E).some.symm⟩

theorem PolarizationData.PolarizedAbelianWithFullLevel.baseChanged_familyComparisonIso_poincare
    (e : (A.pullback f).abelian.scheme ≅ (B.pullback f).abelian.scheme) [IsMonHom e.hom] :
    Line.Bundles.LineBundle.pullbackClass
      (((A.pullback f).dual.familyComparisonIso (B.pullback f).dual e).hom ⊗ₘ e.hom).left
      (Line.Bundles.LineBundle.classOf (B.pullback f).dual.poincare) = Line.Bundles.LineBundle.classOf (A.pullback f).dual.poincare := by
  let D := (A.pullback f).dual
  let E := (B.pullback f).dual
  let d := (D.familyComparisonIso E e).hom
  let l := 𝟙 D.abelian.scheme ⊗ₘ e.hom
  have h := B.baseChanged_uniqueDualIso_poincare_class f (D.familyTransport e) E
  change Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 (B.pullback f).abelian.scheme).left (Line.Bundles.LineBundle.classOf E.poincare) =
    Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.inv).left (Line.Bundles.LineBundle.classOf D.poincare) at h
  have hl : l ≫ (d ⊗ₘ 𝟙 (B.pullback f).abelian.scheme) = d ⊗ₘ e.hom := by
    simpa only [l, id_tensorHom, tensorHom_id] using (tensorHom_def' d e.hom).symm
  have hr : l ≫ (𝟙 D.abelian.scheme ⊗ₘ e.inv) = 𝟙 _ := by simp [l]
  have H := congrArg (Line.Bundles.LineBundle.pullbackClass l.left) h
  rw [← Line.Bundles.LineBundle.pullbackClass_comp, ← Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, hl, hr, Over.id_left, Line.Bundles.LineBundle.pullbackClass_id] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
