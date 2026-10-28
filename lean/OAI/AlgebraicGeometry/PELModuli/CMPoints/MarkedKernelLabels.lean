import OAI.AlgebraicGeometry.PELModuli.CMPoints.PointwiseComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedCoefficientLabel

/-! # Marked Kernel Labels -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedKernelLabels

noncomputable section

/-! Each full integral marking of an actual PEL fiber produces one
of the countable rational labels, with exact equality of its native
period kernel and the coefficient-period equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

theorem exists_PEL_marked_kernel_label
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] {s N n : ℕ}
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (hP : P.IsAdmissible)
    {iota : E →+* K} {T : Over (Spec (.of K))}
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (p : Spec (.of ℂ) ⟶ T.left) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom κ))
    (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n)
      (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (A.polarized.pullback p).abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.polarized.pullback p)))) :
    ∃ (i : RationalCoefficientLabels.RationalCoefficientLabel P n) (z : P.Domain), ∀ v : Fin n → ℂ,
      ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b v = 0 ↔
        ClosedCoefficientPeriods.componentPrescribed P i.val.2 (i.normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (i.coordinates hP v) := by
  let B := A.polarized.pullback p
  let B₀ := AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B)
  let a := IntrinsicCoefficientCoordinates.nativeRationalCoefficientCoordinates B (A.action.pullback p) s hs rfl hdegree
  let H := A.complexFiberHermitianMatrix hs hdegree p
  obtain ⟨e, he⟩ := A.complexFiberHermitianMatrix_normalizer hs hdegree p κ hκ hp hP
  let i : RationalCoefficientLabels.RationalCoefficientLabel P n :=
    ⟨((MarkedRationalPeriods.markedRationalPeriodCoordinates B₀ b).symm.trans a, H),
      A.complexFiberHermitianMatrix_symmetry hs hdegree p hP, e, he⟩
  obtain ⟨z, hz⟩ := PointwiseComparison.exists_PEL_fiber_coefficient_comparison hP A hs hdegree p κ hκ hp
    i.normalizer i.normalizer_spec
  refine ⟨i, z, ?_⟩
  intro v
  let u := (MarkedRationalPeriods.markedComplexPeriodCoordinates B₀ b).symm v
  have h₁ : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b v = 0 ↔ u ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B₀).holomorphic := by
    change ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b v = 0 ↔ AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B₀ u = 0
    rw [MarkedRationalPeriods.markedComplexPeriodCoordinates_projection]
  have h₂ : u ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B₀).holomorphic ↔
      (a.baseChange ℚ ℂ _ _) u ∈
        (IntrinsicCoefficientRealization.nativeCoefficientHodgeStructure B (A.action.pullback p) s hs rfl hdegree).holomorphic :=
    ((AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B₀).transport_holomorphic a u).symm
  have hc : i.coordinates hP v = PeriodCoordinates.cmPeriodCoordinates P hP ((a.baseChange ℚ ℂ _ _) u) := by
    have h := MarkedCoefficientLabel.marked_coefficient_label_coordinates P hP B₀ b a i rfl u
    simpa only [u, LinearEquiv.apply_symm_apply] using h
  exact h₁.trans (h₂.trans ((hz ((a.baseChange ℚ ℂ _ _) u)).trans (by rw [hc])))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedKernelLabels
