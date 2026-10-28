import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicCoefficientPatch
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientPatch
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalCoefficientLabels

/-! # Fixed Holomorphic Coefficient Patch -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedHolomorphicCoefficientPatch

noncomputable section

/-! Pointwise actual coefficient comparisons yield one fixed rational
label and a holomorphic exact period comparison on a nonempty open set. -/

open Set
open scoped Classical

theorem exists_fixed_holomorphic_coefficient_patch
    {E S : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    {s n : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (U : Set S) (hU : IsOpen U) (hne : U.Nonempty)
    (k : S → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (hk : DifferentiableOn ℂ k U)
    (hdim : ∀ q ∈ U, Module.finrank ℂ (k q).range = 3 * s)
    (hcover : ∀ q ∈ U, ∃ (i : RationalCoefficientLabels.RationalCoefficientLabel P n) (z : P.Domain), ∀ v : Fin n → ℂ,
      ClosedCoefficientPeriods.componentPrescribed P i.val.2 (i.normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (i.coordinates hP (k q v))) :
    ∃ (i : RationalCoefficientLabels.RationalCoefficientLabel P n) (O : Set S) (period : S → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ O.Nonempty ∧ O ⊆ U ∧ DifferentiableOn ℂ period O ∧
      (∀ q ∈ O, period q ∈ P.domain) ∧
      ∀ q ∈ O, ∀ v : Fin n → ℂ, v ∈ (k q).range ↔
        ClosedCoefficientPeriods.componentPrescribed P i.val.2 (i.normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector (period q))) (i.coordinates hP v) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : Nonempty U := hne.to_subtype
  obtain ⟨i, O, hO, hOn, hrel⟩ := FixedCoefficientPatch.exists_fixed_coefficient_patch P
    (fun i : RationalCoefficientLabels.RationalCoefficientLabel P n => i.val.2) (fun i => i.normalizer)
    (fun i => (i.coordinates hP).toLinearMap.toContinuousLinearMap)
    (fun q : U => k q) hk.continuousOn.domRestrict (fun q => hcover q q.property)
  let W := Subtype.val '' O
  have hW : IsOpen W := hU.isOpenMap_subtype_val O hO
  have hWU : W ⊆ U := by rintro _ ⟨q, _, rfl⟩; exact q.property
  have hrelW : ∀ q ∈ W, ∃ z : P.Domain, ∀ v : Fin n → ℂ,
      ClosedCoefficientPeriods.componentPrescribed P i.val.2 (i.normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (i.coordinates hP (k q v)) := by
    rintro _ ⟨q, hq, rfl⟩
    exact hrel q hq
  obtain ⟨q₀, hq₀⟩ := hOn
  obtain ⟨V, period, hV, hqV, hVW, hperiod, hdomain, hcomp⟩ :=
    HolomorphicCoefficientPatch.exists_holomorphic_coefficient_patch P hP i.val.2 i.normalizer i.normalizer_spec
      (i.coordinates hP) k W hW (hk.mono hWU) (fun q hq => hdim q (hWU hq))
      hrelW q₀ ⟨q₀, hq₀, rfl⟩
  exact ⟨i, V, period, hV, ⟨q₀, hqV⟩, hVW.trans hWU, hperiod, hdomain, hcomp⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedHolomorphicCoefficientPatch
