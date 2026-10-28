import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MixedPeriodCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RiemannAdjoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodEmbeddingChanges
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine

/-! # Real Period Changes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.RealPeriodChanges.IntrinsicPELRealChanges

noncomputable section

/-! Selected-place unitary maps act on the actual real period space of
any complex PEL object. They commute with its original integral action
and preserve the exact real Chern pairing of its ample polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open _root_.NumberField _root_.NumberField.mixedEmbedding

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A
local notation "B" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA

def rationalMarking : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B ≃ₗ[ℚ] (Fin 3 → E) := by
  letI := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  letI := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  exact (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree).restrictScalars ℚ

omit [IsCMField E] in
theorem rationalMarking_action (a : NumberField.RingOfIntegers E) (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) :
    rationalMarking A ρ s hs hg hdegree (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.abelian PA ρ a x) =
      (a : E) • rationalMarking A ρ s hs hg hdegree x := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  change Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.abelian PA ρ a x) = _
  rw [← Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply]
  exact (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree).map_smul (a : E) x

variable {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

def changeMap (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B :=
  Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E B σ hσ (rationalMarking A ρ s hs hg hdegree) q

attribute [local irreducible] Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange

omit [Fintype Place] in
theorem changeMap_commutes (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (a : NumberField.RingOfIntegers E) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) :
    changeMap A ρ s hs hg hdegree σ hσ q (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.abelian PA ρ a x) =
      Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.abelian PA ρ a (changeMap A ρ s hs hg hdegree σ hσ q x) := by
  let f := (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.abelian PA ρ a).restrictScalars ℝ
  let r := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.abelian PA ρ a
  have hf : ∀ y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B, f y.val = (r y).val := fun _ => rfl
  have hr : ∀ y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B,
      rationalMarking A ρ s hs hg hdegree (r y) =
        (a : E) • rationalMarking A ρ s hs hg hdegree y :=
    rationalMarking_action A ρ s hs hg hdegree a
  have h := Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange_commutes E B σ hσ
    (rationalMarking A ρ s hs hg hdegree) q f r hf (a : E) hr x
  simp only [f, LinearMap.restrictScalars_apply] at h
  dsimp only [changeMap, Module.End]
  exact h

theorem realChernForm_trace (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) :
    TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector B (Intrinsic.ChernPairing.polarizationLineBundle A)) x.val y.val =
      (Algebra.trace ℚ E (ξ * Datum.RankThreePELDatum.matrixHermitian
        (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ)
        (rationalMarking A ρ s hs hg hdegree x)
        (rationalMarking A ρ s hs hg hdegree y)) : ℝ) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  let e := Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree
  have h := Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_trace A ρ s hs hg hdegree hρ ξ hξ (e x) (e y)
  change Algebra.trace ℚ E (ξ * Datum.RankThreePELDatum.matrixHermitian
    (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) (e x) (e y)) =
      Intrinsic.ChernPairing.nativePolarizationForm A (e.symm (e x)) (e.symm (e y)) at h
  rw [e.symm_apply_apply, e.symm_apply_apply] at h
  exact (Intrinsic.RiemannAdjoints.nativeChernForm_real B (Intrinsic.ChernPairing.polarizationLineBundle A) x y).trans
    (congrArg (fun z : ℚ => (z : ℝ)) h.symm)

omit [Fintype Place] in
theorem changeMap_chern (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hq : ∀ p x y, Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) (q p x) (q p y) =
        Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom
          (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y)
    (x y : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) :
    TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector B (Intrinsic.ChernPairing.polarizationLineBundle A))
      (changeMap A ρ s hs hg hdegree σ hσ q x)
      (changeMap A ρ s hs hg hdegree σ hσ q y) =
        TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector B (Intrinsic.ChernPairing.polarizationLineBundle A)) x y :=
  Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange_preserves_trace E B σ hσ (rationalMarking A ρ s hs hg hdegree)
    (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) ξ
    (TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector B (Intrinsic.ChernPairing.polarizationLineBundle A)))
    (realChernForm_trace A ρ s hs hg hdegree hρ ξ hξ) q hq x y

omit [Fintype Place] in
theorem changeMap_riemann (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hq : ∀ p x y, Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) (q p x) (q p y) =
        Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom
          (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y)
    (x y : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) :
    (Intrinsic.RiemannForm.nativeRiemannForm B (Intrinsic.ChernPairing.polarizationLineBundle A) (Intrinsic.ChernPairing.polarizationLineBundle_ample A)
      (changeMap A ρ s hs hg hdegree σ hσ q x)
      (changeMap A ρ s hs hg hdegree σ hσ q y)).im =
        (Intrinsic.RiemannForm.nativeRiemannForm B (Intrinsic.ChernPairing.polarizationLineBundle A) (Intrinsic.ChernPairing.polarizationLineBundle_ample A) x y).im := by
  exact changeMap_chern A ρ s hs hg hdegree σ hσ hρ ξ hξ q hq x y

omit [Fintype Place] in
theorem changedLattice_action_stable (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (a : NumberField.RingOfIntegers E) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hx : changeMap A ρ s hs hg hdegree σ hσ q x ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) :
    changeMap A ρ s hs hg hdegree σ hσ q (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.abelian PA ρ a x) ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B := by
  rw [changeMap_commutes]
  exact Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction_preserves A.abelian PA ρ a _ hx

omit [IsCMField E] in
theorem embeddingInclusion_native (τ : E →ₐ[ℚ] ℂ) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Real.PeriodEmbeddingChanges.complexEmbeddingInclusion B E (rationalMarking A ρ s hs hg hdegree) τ v =
      ((Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree τ).symm v).val := rfl

omit [IsCMField E] in
theorem embeddingInclusion_kernel (τ : E →ₐ[ℚ] ℂ) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B
      (Real.PeriodEmbeddingChanges.complexEmbeddingInclusion B E (rationalMarking A ρ s hs hg hdegree) τ v) = 0 ↔
        v ∈ Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ := by
  rw [embeddingInclusion_native]
  unfold Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart
  rw [Submodule.mem_map_equiv]
  rfl

omit [IsCMField E] in
theorem normalizedEmbeddingInclusion_kernel (τ : E →ₐ[ℚ] ℂ)
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B
      (Real.PeriodEmbeddingChanges.complexEmbeddingInclusion B E (rationalMarking A ρ s hs hg hdegree) τ (e₀ v)) = 0 ↔
        v ∈ Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine A ρ s hs hg hdegree τ e₀ := by
  rw [embeddingInclusion_kernel]
  unfold Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine
  rw [Submodule.mem_map_equiv]
  rfl

omit [Fintype Place] in
theorem changed_normalized_kernel
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (d : Place)
    (e₀ r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hq : ∀ v, q d (e₀ v) = e₀ (r v)) (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine A ρ s hs hg hdegree (σ d) e₀ =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hw : (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}).map r.toLinearMap =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w}) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Real.PeriodHodgeTransport.realChangedComplexPeriodMap B (changeMap A ρ s hs hg hdegree σ hσ q)
        ((rationalMarking A ρ s hs hg hdegree).symm.toLinearMap.baseChange ℂ
          (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E (σ d) e₀ v)) = 0 ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} := by
  apply Real.PeriodEmbeddingChanges.realChanged_firstKernel B E σ hσ (rationalMarking A ρ s hs hg hdegree)
    q d e₀ r hq z w _ hw v
  intro x
  exact (normalizedEmbeddingInclusion_kernel A ρ s hs hg hdegree (σ d) e₀ x).trans
    (by rw [hz])

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.RealPeriodChanges.IntrinsicPELRealChanges
