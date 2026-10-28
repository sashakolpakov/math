import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.TranslationKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelUnramifiedOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementParameterPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.UnramifiedFieldCriterion

/-! # Translation Kernel Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.TranslationKernelOpen.GraphPowerPolarizationEnhancement

noncomputable section

/-! Every original graph-power enhancement lands in the unramified
translation-kernel open when twice the graph exponent is invertible. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem unramified_of_over_iso
    {S : Scheme.{0}} {X Y : Over S} (e : X ≅ Y)
    (hY : FormallyUnramified Y.hom) : FormallyUnramified X.hom := by
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have h : FormallyUnramified (e.hom.left ≫ Y.hom) :=
    MorphismProperty.comp_mem (@FormallyUnramified) e.hom.left Y.hom inferInstance hY
  exact e.hom.w ▸ h

variable {S : Scheme.{0}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N S) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ) (hδ : ∀ i, 0 < δ i)
    (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    {T : Scheme.{0}} (b : T ⟶ S)
    (H : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback b)
      ((F.abelian.zeroNormalizedBundle L).pullback (pullback.fst F.abelian.scheme.hom b)) d)

include hδ hunit H in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.range_translationKernelUnramifiedOpen :
    Set.range b ⊆ TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen F.abelian L P := by
  apply (TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen_all_tests F.abelian L P b).mpr
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily F.abelian L P
  have : IsProper Z.hom := TranslationKernelProper.translationKernel_proper F.abelian L P
  change FormallyUnramified (pullback.snd Z.hom b)
  apply Geometric.UnramifiedFieldCriterion.formallyUnramified_of_geometricFieldPullbacks
  intro K _ _ c
  let q := c ≫ b
  let a : Over.mk q ⟶ Over.mk b := Over.homMk c rfl
  let Hq := PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullback
    (F := F) (L := F.abelian.zeroNormalizedBundle L)
    (T := Over.mk b) (U := Over.mk q) H a
  let Lq := L.pullback (pullback.fst F.abelian.scheme.hom q)
  let Hn := Hq.ofBundleIso (F.abelian.zeroNormalizedBundle_baseChangeIso L q).symm
  have huq : IsUnit ((2 * d : ℕ) : Γ(Spec (.of K), ⊤)) :=
    Abelian.Schemes.level_unit_under_base_change q (2 * d) hunit
  let Zq := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (F.abelian.pullback q) Lq (P.baseChange q)
  have hEt : Etale Zq.hom := TranslationKernel.graphPower_field_translationKernel_etale F.abelian P q
    (F.level.pullback q) δ hδ Lq d huq Hn
  have hq : FormallyUnramified Zq.hom := (Etale.iff_flat_and_formallyUnramified.mp hEt).2.1
  obtain ⟨e, _⟩ := Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric.exists_translationZero_baseChange_iso F.abelian L P q (P.baseChange q)
  have : FormallyUnramified (pullback.snd Z.hom q) :=
    unramified_of_over_iso (X := (Over.pullback q).obj Z) (Y := Zq) e hq
  exact UnramifiedPullbackRefinements.unramified_iterated_pullback Z.hom b c

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.translationKernelUnramifiedOpenLift :
    T ⟶ TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen F.abelian L P :=
  IsOpenImmersion.lift (TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen F.abelian L P).ι b (by
    simpa only [Scheme.Opens.range_ι] using
      PolarizationEnhancementData.GraphPowerPolarizationEnhancement.range_translationKernelUnramifiedOpen F P L d hδ hunit b H)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.translationKernelUnramifiedOpenLift_ι :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement.translationKernelUnramifiedOpenLift F P L d hδ hunit b H ≫
      (TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen F.abelian L P).ι = b :=
  IsOpenImmersion.lift_fac _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.TranslationKernelOpen.GraphPowerPolarizationEnhancement
