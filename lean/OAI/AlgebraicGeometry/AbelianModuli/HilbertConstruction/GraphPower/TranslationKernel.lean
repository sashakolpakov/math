import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.MultipleIsogeny
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.InducingHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.TranslationDivisorPolarization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingMap

/-! # Translation Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.TranslationKernel

noncomputable section

/-! On an enhanced geometric fiber, the original translation kernel is
the scheme-theoretic kernel of the exact composite [2d]p. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

local instance (X : Scheme.{0}) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup X

private theorem relativeDifference_class_normalized
    {S : Scheme.{0}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left) :
    Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) =
      Picard.PoincareBundle.InducingClass.Bundle.lineClass A.scheme (A.zeroNormalizedBundle L) := by
  have h := Picard.PoincareBundle.InducingClass.Bundle.class_eq_of_formula A.scheme
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L) (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle_formula A L).some
  have hn : Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L) =
      Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L) :=
    Quotient.sound ⟨Rational.TranslationDivisorPolarization.identityNormalizationComparison A L⟩
  simpa only [Picard.PoincareBundle.InducingClass.Bundle.lineClass, hn] using h

variable {S : Scheme.{0}} [IsNoetherian S] {g N : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    {K : Type} [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)
    (level : (A.pullback b).FullLevel N) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)
    (L : Line.Bundles.LineBundle (A.pullback b).scheme.left) (d : ℕ)
    (hunit : IsUnit ((2 * d : ℕ) : Γ(Spec (.of K), ⊤)))
    (H : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      (⟨A.pullback b, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N (Spec (.of K)))
      ((A.pullback b).zeroNormalizedBundle L) d)

include hδ in
theorem graphPower_field_translationKernel_iso :
    ∃ e : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (A.pullback b) L (P.baseChange b) ≅
        (H.polarization.isogeny.unitMultiple (2 * d) hunit).kernelScheme,
      e.hom ≫ (H.polarization.isogeny.unitMultiple (2 * d) hunit).kernelInclusion =
        Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion (A.pullback b) L (P.baseChange b) := by
  let B := A.pullback b
  let M := B.zeroNormalizedBundle L
  let m := Picard.PoincareBundle.InducingMap.hom H.dual M
  let : IsMonHom m := Picard.PoincareBundle.InducingMap.hom_isMonHom H.dual M
  obtain ⟨em⟩ := Picard.PoincareBundle.InducingMap.exists_familyIso H.dual M
    (B.zeroNormalizedBundle_zeroIso L)
  rw [tensorHom_id] at em
  let ef : (((H.dual.poincareAt m).tensor
      (M.pullback (fst B.scheme B.scheme).left)).tensor
      (M.pullback (snd B.scheme B.scheme).left)).sheaf ≅
        (M.pullback μ[B.scheme].left).sheaf :=
    Tensor.ProductSheaf.tensorModuleCongr (Tensor.ProductSheaf.tensorModuleCongr em.symm (Iso.refl _)) (Iso.refl _) ≪≫
      Picard.PoincareBundle.InducingClass.Bundle.formula B.scheme M
  have hm : B.multiplication (2 * d) ≫ H.polarization.isogeny.hom = m :=
    InducingHom.polarization_inducingHom_eq_multiple_of_graphPower A P (Over.mk b) H.dual H.polarization
      level hδ m (IsMonHom.one_hom m) M d ef H.powerIso.some
  have hem : Line.Bundles.LineBundle.classOf (H.dual.poincareAt m) =
      Line.Bundles.LineBundle.classOf (Picard.PoincareBundle.InducingClass.Bundle.line B.scheme M) :=
    Quotient.sound ⟨em.symm⟩
  have hc : Line.Bundles.LineBundle.classOf (H.dual.poincareAt m) =
      Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle B L) :=
    hem.trans
      ((Picard.PoincareBundle.InducingClass.Bundle.classOf_line B.scheme M).trans
        (relativeDifference_class_normalized B L).symm)
  apply TranslationKernelComparison.translationKernel_iso_of_poincare_class H.dual
    (H.polarization.isogeny.unitMultiple (2 * d) hunit) L (P.baseChange b)
  rw [Abelian.Schemes.AbelianScheme.Isogeny.unitMultiple_hom, hm]
  exact hc

include hδ hunit H in
theorem graphPower_field_translationKernel_etale :
    Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (A.pullback b) L (P.baseChange b)).hom := by
  let m := H.polarization.isogeny.unitMultiple (2 * d) hunit
  have : Etale H.polarization.isogeny.hom.left := H.polarization.kernelType.etale hδ
  have : Etale m.hom.left := inferInstance
  have : Etale m.kernelScheme.hom :=
    inferInstanceAs (Etale (pullback.snd m.hom.left η[H.dual.abelian.scheme].left))
  obtain ⟨e, _⟩ := graphPower_field_translationKernel_iso A P b level δ hδ L d hunit H
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map e.hom))
  have he : Etale (e.hom.left ≫ m.kernelScheme.hom) := inferInstance
  exact e.hom.w ▸ he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.TranslationKernel
