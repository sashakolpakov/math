import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedHolomorphicCoefficientPatch
import OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedKernelLabels
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLabelRealization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodFiberCountability
import OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedPeriodKernel
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicKernelProjection
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalCoordinateFiber

/-! # Intrinsic Period Matrix Fiber -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodMatrixFiber

noncomputable section

/-! Holomorphic matrices of the actual full marked PEL periods
produce a fiber with the specified coordinate CM realization. All
coefficient labels, local ball coordinates, and countable fibers are
constructed from those native matrices and the original fine model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.CategoryTheory.MonObj

theorem exists_coordinate_CM_fiber_of_native_period_matrices
    {E K F : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] [NumberField K]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {s N r n d : ℕ} [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (hP : P.IsAdmissible) (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (basis : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    (U : Set F) (hU : IsOpen U) (hne : U.Nonempty)
    (hdimF : Module.finrank ℂ F = Module.finrank ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (p : F → (Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ M.space))
    (hp : Set.InjOn p U)
    (b : ∀ q : U, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n)
      (PolarizedIntrinsicPresentation.polarizedNativePresentation (M.universal.pullback (p q)).polarized).variety)
    (matrix : F → (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (hhol : DifferentiableOn ℂ matrix U)
    (hsurj : ∀ q : U, Function.Surjective (matrix q))
    (hker : ∀ q : U, (matrix q).ker = (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b q)).ker) :
    ∃ q : U, CoordinateRealization.HasCoordinateCMRealization P hP
      (PolarizedIntrinsicPresentation.polarizedNativePresentation (M.universal.pullback (p q)).polarized).variety := by
  obtain ⟨q₀, hq₀⟩ := hne
  obtain ⟨W, k, hW, hqW, hWU, hk, hkr⟩ := HolomorphicKernelProjection.exists_holomorphic_kernel_projection
    matrix U hU hhol q₀ hq₀ (hsurj ⟨q₀, hq₀⟩)
  have hdim (q : F) (hq : q ∈ W) : Module.finrank ℂ (k q).range = 3 * s := by
    rw [(hkr q hq).1, hker ⟨q, hWU hq⟩, MarkedPeriodKernel.markedPeriodKernel_finrank]
    exact AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq (M.universal.pullback (p q)).polarized.abelian
  have hcover (q : F) (hq : q ∈ W) :
      ∃ (i : RationalCoefficientLabels.RationalCoefficientLabel P n) (z : P.Domain), ∀ v : Fin n → ℂ,
        ClosedCoefficientPeriods.componentPrescribed P i.val.2 (i.normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (i.coordinates hP (k q v)) := by
    obtain ⟨i, z, hz⟩ := MarkedKernelLabels.exists_PEL_marked_kernel_label hP M.universal hs hdegree
      (p q).left κ hκ (p q).w (b ⟨q, hWU hq⟩)
    refine ⟨i, z, fun v => (hz (k q v)).mp ?_⟩
    have hm : k q v ∈ (k q).range := ⟨v, rfl⟩
    rw [(hkr q hq).1, hker ⟨q, hWU hq⟩] at hm
    exact hm
  obtain ⟨i, O, period, hO, hOn, hOW, hperiod, hdomain, hcomp⟩ :=
    FixedHolomorphicCoefficientPatch.exists_fixed_holomorphic_coefficient_patch P hP W hW ⟨q₀, hqW⟩ k hk hdim hcover
  have hOU : O ⊆ U := hOW.trans hWU
  let bO := fun q : O => b ⟨q.val, hOU q.property⟩
  have hc (q : O) (v : Fin n → ℂ) : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (bO q) v = 0 ↔
      ClosedCoefficientPeriods.componentPrescribed P i.val.2 (i.normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector (period q))) (i.coordinates hP v) := by
    have h := hcomp q q.property v
    rw [(hkr q (hOW q.property)).1, hker ⟨q, hOU q.property⟩] at h
    exact h
  have hcount : ∀ z, {q : F | q ∈ O ∧ period q = z}.Countable := by
    have h := PeriodFiberCountability.PEL_period_fibers_countable M hM κ basis (fun q : O => p q)
      (by intro q q' hq; exact Subtype.ext (hp (hOU q.property) (hOU q'.property) hq))
      bO i.val.2 i.normalizer (i.coordinates hP) (fun q : O => period q) hc
    intro z
    apply ((h z).image (fun q : O => q.val)).mono
    intro q hq
    exact ⟨⟨q, hq.1⟩, hq.2, rfl⟩
  let A := fun q : O => (M.universal.pullback (p q)).polarized
  let B := fun q : O => (PolarizedIntrinsicPresentation.polarizedNativePresentation (A q)).variety
  let H := fun q : O => IntrinsicLabelRealization.nativeLabelHodge (B q) (bO q) i
  let R := fun q : O => IntrinsicLabelRealization.nativeLabelRealization (B q) (bO q) i
    (AbelianModuli.ReferenceFamily.Intrinsic.PeriodPolarization.nativePeriodPolarization (B q) (AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle (A q)) (AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle_ample (A q)))
  obtain ⟨q, hq⟩ := LocalCoordinateFiber.exists_coordinate_CM_fiber_of_local_holomorphic_comparison P hP
    O hO hOn hdimF i.val.2 i.property.1 i.normalizer i.normalizer_spec
    period hperiod hcount hdomain H R
    (fun q x => IntrinsicLabelRealization.nativeLabelHodge_holomorphic (B q) (bO q) i hP (period q) (hc q) x)
  exact ⟨⟨q.val, hOU q.property⟩, hq⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodMatrixFiber
