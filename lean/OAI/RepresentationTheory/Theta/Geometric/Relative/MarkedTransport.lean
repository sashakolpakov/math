import OAI.RepresentationTheory.Theta.Geometric.Relative.NormalizedHodgeLines
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv

/-! # Marked Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Equal distinguished normalized lines determine the full actual
Hodge transport: compact and conjugate embedding blocks are forced by
the original signature and Hermitian polarization. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.markedBetween (z w : D.neighborhood) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety ≃ₗ[ℚ]
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left))
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left))
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    s hs hg hdegree (D.coordinateBetween A ρ s hs hg hdegree z w)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.markedBetween_isHodgeMap (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (τ : Fin s → E →ₐ[ℚ] ℂ) (d : Fin s)
    (hτ : Function.Surjective (fun p : Fin s × Bool => if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ p.1) else τ p.1))
    (e₀ : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (z w : D.neighborhood)
    (hline : D.normalizedHodgeLine A ρ s hs hg hdegree (τ d) e₀ z =
      D.normalizedHodgeLine A ρ s hs hg hdegree (τ d) e₀ w)
    (hc : ∀ i, i ≠ d → ∃ r, (r = 0 ∨ r = 3) ∧
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
        (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
        ((τ i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r ∧
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
        (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
        ((τ i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety)
      (D.markedBetween A ρ s hs hg hdegree z w).toLinearMap := by
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion.NativeHermitianMarking.markedPeriodTransport_isHodgeMap_of_CMType
    (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    s hs hg hdegree (hρ.pullback A ρ (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (hρ.pullback A ρ (Intrinsic.FamilyFrames.familyChartParameter C w).left) ξ hξ
    (D.coordinateBetween A ρ s hs hg hdegree z w) τ hτ
    (D.coordinateBetween_hermitian A ρ s hs hg hdegree hρ ξ hξ z w)
  intro i
  by_cases hi : i = d
  · subst i
    exact D.positivePart_between_of_normalized_eq A ρ s hs hg hdegree (τ d) e₀ z w hline
  · obtain ⟨r, hr, hz, hw⟩ := hc i hi
    exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking.nativePositivePart_map_of_extreme_ranks (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
      (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) s hs hg hdegree (τ i)
      (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left) (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
      (D.coordinateBetween A ρ s hs hg hdegree z w) hr hz hw

end

section

/-! Exact rational coordinate formulas for the marked comparison of
any two fibers in the same constructed native frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.markedBetween_coordinates (z w : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) :
    Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C w) s hs hg hdegree
      (D.markedBetween A ρ s hs hg hdegree z w v) =
      D.coordinateBetween A ρ s hs hg hdegree z w
        (Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree v) := by
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates
    (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left))
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left))
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    s hs hg hdegree (D.coordinateBetween A ρ s hs hg hdegree z w) v

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.PELCoordinates.familyPELCoordinates Family.FieldActions.familyFieldPeriodAction

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.markedBetween_apply_center (z w : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety) :
    D.markedBetween A ρ s hs hg hdegree z w
      (F.nativeRationalTransport z (D.subset_frame z.property) (D.subset_chart z.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) v) =
      F.nativeRationalTransport w (D.subset_frame w.property) (D.subset_chart w.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)) v := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C w)
  apply (Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C w) s hs hg hdegree).injective
  have hz := D.coordinateTransport_apply A ρ s hs hg hdegree z v
  have hw := D.coordinateTransport_apply A ρ s hs hg hdegree w v
  let c₀ := Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree
  have hu : D.coordinateBetween A ρ s hs hg hdegree z w
      (D.coordinateTransport A ρ s hs hg hdegree z (c₀ v)) =
      D.coordinateTransport A ρ s hs hg hdegree w (c₀ v) :=
    congrArg (D.coordinateTransport A ρ s hs hg hdegree w)
      ((D.coordinateTransport A ρ s hs hg hdegree z).symm_apply_apply (c₀ v))
  exact (D.markedBetween_coordinates A ρ s hs hg hdegree z w _).trans
    ((congrArg (D.coordinateBetween A ρ s hs hg hdegree z w) hz.symm).trans (hu.trans hw))

end

/-! The marked comparison is exactly the composition of the original
native rational transports through their common central fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.rationalBetween (z w : D.neighborhood) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety ≃ₗ[ℚ]
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety :=
  (F.nativeRationalEquiv z (D.subset_frame z.property) (D.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))).symm.trans
      (F.nativeRationalEquiv w (D.subset_frame w.property) (D.subset_chart w.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)))

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.rationalBetween_apply_center (z w : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety) :
    D.rationalBetween A ρ z w
      (F.nativeRationalTransport z (D.subset_frame z.property) (D.subset_chart z.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) v) =
      F.nativeRationalTransport w (D.subset_frame w.property) (D.subset_chart w.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)) v :=
  congrArg (F.nativeRationalEquiv w (D.subset_frame w.property) (D.subset_chart w.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)))
    ((F.nativeRationalEquiv z (D.subset_frame z.property) (D.subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))).symm_apply_apply v)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.markedBetween_eq_rationalBetween (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) (z w : D.neighborhood) :
    D.markedBetween A ρ s hs hg hdegree z w = D.rationalBetween A ρ z w := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨v₀, rfl⟩ := (F.nativeRationalEquiv z (D.subset_frame z.property) (D.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))).surjective v
  exact (D.markedBetween_apply_center A ρ s hs hg hdegree z w v₀).trans
    (D.rationalBetween_apply_center A ρ z w v₀).symm

end

end OAI.RepresentationTheory.Theta.Geometric
