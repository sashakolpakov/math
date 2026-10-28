import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.BoundProjectiveGlobalDual
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.EtaleTranslationKernelQuotient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelProper
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationZeroBaseChange

/-! # Unramified Projective Global Dual -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedProjectiveGlobalDual

noncomputable section

/-! The actual unramified translation kernel is finite etale under the
field H1 bound. Its effective affine quotients glue to the original
dual abelian scheme with the complete all-test Picard universal property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric

theorem fieldBoundTranslationKernel_finite
    {S : Scheme} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (hH1 : A.HasFieldStructureH1Bound)
    [FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom] :
    IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  have : IsProper (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := TranslationKernelProper.translationKernel_proper A L P
  have : Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom :=
    Field.BoundProjectiveDual.fieldBoundTranslationKernel_etale A L P hH1
  have : LocallyQuasiFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom :=
    UnramifiedQuasiFinite.locallyQuasiFinite_of_unramified _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem translationKernel_etale_baseChange
    {S S' : Scheme} [IsLocallyNoetherian S] [IsLocallyNoetherian S'] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : S' ⟶ S)
    (P' : Projective.ProjectivePresentations.ProjectivePresentation (A.pullback f).scheme)
    [Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom] :
    Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (A.pullback f)
      (L.pullback (pullback.fst A.scheme.hom f)) P').hom := by
  obtain ⟨e, _⟩ := Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric.exists_translationZero_baseChange_iso A L P f P'
  let Z := (Over.pullback f).obj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P)
  have : Etale Z.hom :=
    inferInstanceAs (Etale (pullback.snd (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom f))
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S').map e.inv))
  have h : Etale (e.inv.left ≫ Z.hom) := inferInstance
  exact e.inv.w ▸ h

theorem fieldBoundLocallyNoetherianProjectiveDual_exists
    {S : Scheme} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hH1 : A.HasFieldStructureH1Bound)
    (hK : FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A P.ampleLineBundle P).hom) :
    ∃ (D : Dual.Data.DualAbelianData A) (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian),
      Etale m.hom.left ∧ Nonempty
        ((D.poincare.pullback (m.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
          (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A P.ampleLineBundle).sheaf) := by
  have : FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A P.ampleLineBundle P).hom := hK
  have : Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A P.ampleLineBundle P).hom :=
    Field.BoundProjectiveDual.fieldBoundTranslationKernel_etale A P.ampleLineBundle P hH1
  apply Field.BoundProjectiveGlobalDual.fieldBoundLocallyNoetherianProjectiveDual_exists_of_chartQuotients A P hH1
  intro i
  have : IsNoetherianRing (S.affineOpenCover.X i) := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian S i
  let f := S.affineOpenCover.f i
  let B := A.pullback f
  let L := Field.BoundProjectiveGlobalDual.FieldBoundProjectiveGlobalDual.chartLine A P i
  let PB := P.baseChange f
  have : Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily B L PB).hom :=
    translationKernel_etale_baseChange A P.ampleLineBundle P f PB
  have : IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily B L PB).hom :=
    fieldBoundTranslationKernel_finite B L PB (hH1.pullback f)
  exact Classical.choice (Finite.EtaleTranslationKernelQuotient.ampleTranslationQuotient_nonempty_of_finite_etale B L PB)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedProjectiveGlobalDual
