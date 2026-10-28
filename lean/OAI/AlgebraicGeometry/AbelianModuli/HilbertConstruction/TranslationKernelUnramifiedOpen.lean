import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelProper
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.UnramifiedBaseOpen
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationZeroBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting

/-! # Translation Kernel Unramified Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelUnramifiedOpen

noncomputable section

/-! The original translation kernel has an unramified open on the base.
Its criterion keeps all test schemes and the original projective line. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

def translationKernelUnramifiedOpen : S.Opens := by
  let : IsProper (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := TranslationKernelProper.translationKernel_proper A L P
  exact Proper.UnramifiedBaseOpen.properUnramifiedBaseOpen (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom

theorem translationKernelUnramifiedOpen_all_tests {T : Scheme.{0}} (b : T ⟶ S) :
    Set.range b ⊆ translationKernelUnramifiedOpen A L P ↔
      FormallyUnramified ((Over.pullback b).obj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P)).hom := by
  let : IsProper (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := TranslationKernelProper.translationKernel_proper A L P
  exact Proper.UnramifiedBaseOpen.properUnramifiedBaseOpen_all_tests (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom b

theorem translationKernel_unramified_of_range_subset
    {T : Scheme.{0}} [IsLocallyNoetherian T] (b : T ⟶ S)
    (hb : Set.range b ⊆ translationKernelUnramifiedOpen A L P)
    (Q : Projective.ProjectivePresentations.ProjectivePresentation (A.pullback b).scheme) :
    FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (A.pullback b)
      (L.pullback (pullback.fst A.scheme.hom b)) Q).hom := by
  let Z := (Over.pullback b).obj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P)
  have : FormallyUnramified Z.hom :=
    (translationKernelUnramifiedOpen_all_tests A L P b).mp hb
  obtain ⟨e, _⟩ := Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric.exists_translationZero_baseChange_iso A L P b Q
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget T).map e.inv))
  have h : FormallyUnramified (e.inv.left ≫ Z.hom) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
  exact e.inv.w ▸ h

theorem projectiveTranslationKernel_unramified_of_range_subset
    {T : Scheme.{0}} [IsLocallyNoetherian T] (b : T ⟶ S)
    (hb : Set.range b ⊆ translationKernelUnramifiedOpen A P.ampleLineBundle P) :
    FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (A.pullback b)
      (P.baseChange b).ampleLineBundle (P.baseChange b)).hom := by
  let M := P.ampleLineBundle.pullback (pullback.fst A.scheme.hom b)
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (A.pullback b) M (P.baseChange b)
  have : FormallyUnramified Z.hom :=
    translationKernel_unramified_of_range_subset A P.ampleLineBundle P b hb (P.baseChange b)
  have hM : Line.Bundles.LineBundle.classOf M = Line.Bundles.LineBundle.classOf (P.baseChange b).ampleLineBundle :=
    Quotient.sound ⟨(P.baseChangeTwistingBundleIso b).symm⟩
  obtain ⟨e, _⟩ := TranslationKernelComparison.translationKernel_iso_of_lineClass (A := A.pullback b) M (P.baseChange b).ampleLineBundle
    (P.baseChange b) (P.baseChange b) hM
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget T).map e.inv))
  have h : FormallyUnramified (e.inv.left ≫ Z.hom) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
  exact e.inv.w ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelUnramifiedOpen
