import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase

/-! # Affine Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AffineCoordinates.OrientedNormalization

noncomputable section

/-! The two affine Hom comparisons evaluate the same original local
sheaf map. The canonical Koszul comparison retains that evaluation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

omit [N.IsQuasicoherent] in
theorem affine_dual_apply (q : ℕ) (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X q) N, U))
    (x : Γ(K.X q, U)) :
    (show Module.Dual Γ(Y, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X q)) from
      (Principal.OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom.f q a)
        ((Affine.ChartSections.iso U hU (K.X q)).hom x) =
      e (Affine.HomEvaluation.evaluation (K.X q) N U a x) := by
  change e ((Affine.ChartSections.iso U hU N).inv
    (Affine.HomEvaluation.chartEvaluation (K.X q) N U hU a
      ((Affine.ChartSections.iso U hU (K.X q)).hom x))) = _
  rw [Affine.HomEvaluation.chart_comparison_apply, Iso.hom_inv_id_apply]

variable {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (Principal.ClosedQuotient.directImage f))
  [QuasiIso ε] [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))

attribute [local instance] Principal.OrientedResidue.structure_quasicoherent

def normalLift := ProjectiveResolution.lift (𝟙 _)
  (KoszulPartial.Resolution.normalResolution Γ(Y, U) s hreg)
  (Affine.OrientedPurity.resolution U hU K (Principal.ClosedQuotient.directImage f) ε
    (KoszulPartial.Resolution.normalIdeal Γ(Y, U) s)
    (Principal.OrientedResidue.quotientIso f U hU s hs))

theorem principal_compare_apply (q : ℕ)
    (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X q) N, U))
    (x : ⋀[Γ(Y, U)]^q (Fin c → Γ(Y, U))) :
    (show (⋀[Γ(Y, U)]^q (Fin c → Γ(Y, U))) →ₗ[Γ(Y, U)]
        Γ(Y, Principal.SectionPresheaf.openSubset U (Principal.AtOne.object U)) from
      ((Principal.Koszul.Comparison.equivalence U hU N e K
        (Principal.ClosedQuotient.directImage f) ε s hreg
        (Principal.OrientedResidue.quotientIso f U hU s hs)).hom.f q).app
          (op (Principal.AtOne.object U)) ((Principal.OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom.f q a)) x =
      algebraMap Γ(Y, U) Γ(Y, Principal.SectionPresheaf.openSubset U (Principal.AtOne.object U))
        (e (Affine.HomEvaluation.evaluation (K.X q) N U a
          ((Affine.ChartSections.iso U hU (K.X q)).inv
            ((normalLift U hU K f ε s hs hreg).f q x)))) := by
  change Principal.LineFrame.frame U hU N e (Principal.AtOne.object U)
      ((show Γ(K.X q, U) →ₗ[Γ(Y, U)] Γ(N, Principal.SectionPresheaf.openSubset U (Principal.AtOne.object U)) from
        (Principal.InternalHom.iso U hU (K.X q) N).hom.app (op (Principal.AtOne.object U))
          ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X q) N).presheaf.map
            (Principal.SectionPresheaf.inclusion U (Principal.AtOne.object U)).op a))
        ((Affine.ChartSections.iso U hU (K.X q)).inv
          ((normalLift U hU K f ε s hs hreg).f q x))) = _
  exact Principal.OrientedResidueNormalizationBase.framed_restriction U hU N e (K.X q) (Principal.AtOne.object U) a _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AffineCoordinates.OrientedNormalization
