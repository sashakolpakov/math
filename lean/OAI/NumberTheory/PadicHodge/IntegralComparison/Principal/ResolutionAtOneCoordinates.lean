import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase

/-! # Resolution At One Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ResolutionAtOneCoordinates

noncomputable section

/-! An arbitrary coefficient resolution comparison evaluates at the
unit principal open through its actual augmentation-preserving lift. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U))
  (M : X.Modules) [M.IsQuasicoherent]
  (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (T : ModuleCat.{u} Γ(X, U)) (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T)
  (P : ProjectiveResolution T)

abbrev lift := ProjectiveResolution.lift (𝟙 T) P
  (Resolution.Comparison.resolution U hU M K ε T eM)

 theorem comparison (q : ℕ)
    (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X q) N, U)) (x : P.complex.X q) :
    (show P.complex.X q →ₗ[Γ(X, U)] Γ(X, SectionPresheaf.openSubset U (AtOne.object U)) from
      ((Resolution.Comparison.equivalence U hU N e M K ε T eM P).hom.f q).app
        (op (AtOne.object U))
          ((OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom.f q a)) x =
    algebraMap Γ(X, U) Γ(X, SectionPresheaf.openSubset U (AtOne.object U))
      (e (Affine.HomEvaluation.evaluation (K.X q) N U a
        ((Affine.ChartSections.iso U hU (K.X q)).inv
          ((ResolutionAtOneCoordinates.lift U hU M K ε T eM P).f q x)))) := by
  change LineFrame.frame U hU N e (AtOne.object U)
      ((show Γ(K.X q, U) →ₗ[Γ(X, U)] Γ(N, SectionPresheaf.openSubset U (AtOne.object U)) from
        (InternalHom.iso U hU (K.X q) N).hom.app (op (AtOne.object U))
          ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X q) N).presheaf.map
            (SectionPresheaf.inclusion U (AtOne.object U)).op a))
        ((Affine.ChartSections.iso U hU (K.X q)).inv
          ((ResolutionAtOneCoordinates.lift U hU M K ε T eM P).f q x))) = _
  exact OrientedResidueNormalizationBase.framed_restriction U hU N e (K.X q)
    (AtOne.object U) a _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ResolutionAtOneCoordinates
