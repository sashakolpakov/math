import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.EmbeddingMatrices
import OAI.RepresentationTheory.Theta.Geometric.Relative.MarkedTransport
import OAI.RepresentationTheory.Theta.Geometric.Relative.LevelIso

/-! # Kernel PEL Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Equality of the constructed distinguished kernels gives an actual
polarized full-level fiber isomorphism, retaining the integral CM action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (τ : Fin s → E →ₐ[ℚ] ℂ) (d : Fin s)
    (hτ : Function.Surjective (fun p : Fin s × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ p.1) else τ p.1))
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z w : H.compatible.neighborhood)
    (heq : (H.embeddingMatrix s hs hg hdegree (τ d) e₀ z).ker =
      (H.embeddingMatrix s hs hg hdegree (τ d) e₀ w).ker)
    (hc : ∀ i, i ≠ d → ∃ r, (r = 0 ∨ r = 3) ∧
      LieRanks.HasLieRank (A.abelian.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
        (ρ.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
        ((τ i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r ∧
      LieRanks.HasLieRank (A.abelian.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w).left)
        (ρ.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w).left)
        ((τ i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r)

include hρ ξ hξ hτ heq hc in
theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.isHodgeMap_of_embeddingKernel_eq :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w)).variety)
      (H.compatible.rationalBetween A ρ z w).toLinearMap := by
  have hline := (H.embeddingMatrix_kernel s hs hg hdegree (τ d) e₀ z).symm.trans
    (heq.trans (H.embeddingMatrix_kernel s hs hg hdegree (τ d) e₀ w))
  have hH := H.compatible.markedBetween_isHodgeMap A ρ s hs hg hdegree hρ ξ hξ τ d hτ e₀ z w hline hc
  rw [H.compatible.markedBetween_eq_rationalBetween A ρ s hs hg hdegree z w] at hH
  exact hH

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.levelIsoOfEmbeddingKernel :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
      (A.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w).left) :=
  H.compatible.levelIso A ρ z w
    (H.isHodgeMap_of_embeddingKernel_eq s hs hg hdegree hρ ξ hξ τ d hτ e₀ z w heq hc)

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.levelIsoOfEmbeddingKernel_action (a : NumberField.RingOfIntegers E) :
    (ρ.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left).map a ≫
        (H.levelIsoOfEmbeddingKernel s hs hg hdegree hρ ξ hξ τ d hτ e₀ z w heq hc).abelian.hom =
      (H.levelIsoOfEmbeddingKernel s hs hg hdegree hρ ξ hξ τ d hτ e₀ z w heq hc).abelian.hom ≫
        (ρ.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w).left).map a :=
  H.compatible.levelIso_action A ρ z w
    (H.isHodgeMap_of_embeddingKernel_eq s hs hg hdegree hρ ξ hξ τ d hτ e₀ z w heq hc) a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
