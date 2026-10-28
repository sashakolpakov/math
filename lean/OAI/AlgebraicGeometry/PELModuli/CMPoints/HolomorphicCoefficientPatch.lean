import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentKernelEquality
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicLineCoordinate
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Holomorphic Coefficient Patch -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicCoefficientPatch

noncomputable section

/-! On a patch with fixed rational coefficient data, the actual
holomorphic kernel determines a holomorphic ball coordinate and the
exact coefficient comparison. -/

open Set
open scoped Classical

theorem exists_holomorphic_coefficient_patch
    {E S V : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [NormedAddCommGroup S] [NormedSpace ℂ S]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (C : V ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (k : S → V →L[ℂ] V)
    (U : Set S) (hU : IsOpen U) (hk : DifferentiableOn ℂ k U)
    (hdim : ∀ q ∈ U, Module.finrank ℂ (k q).range = 3 * s)
    (hcover : ∀ q ∈ U, ∃ z : P.Domain, ∀ v : V,
      ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (C (k q v)))
    (q₀ : S) (hq₀ : q₀ ∈ U) :
    ∃ (O : Set S) (period : S → Geometry.ComplexBall.PrescribedSignsB.BallChart), IsOpen O ∧ q₀ ∈ O ∧ O ⊆ U ∧
      DifferentiableOn ℂ period O ∧
      (∀ q ∈ O, period q ∈ P.domain) ∧
      ∀ q ∈ O, ∀ v : V, v ∈ (k q).range ↔
        ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector (period q))) (C v) := by
  have hfull (q : S) (hq : q ∈ U) (z : P.Domain)
      (hz : ∀ v : V, ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (C (k q v))) :
      ∀ v : V, v ∈ (k q).range ↔ ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (C v) :=
    ComponentKernelEquality.component_kernel_equality_of_inclusion P hP H e he C (k q).range (hdim q hq) z
      (by rintro _ ⟨v, rfl⟩; exact hz v)
  obtain ⟨z₀, hz₀⟩ := hcover q₀ hq₀
  obtain ⟨v₀, hv₀, he₀⟩ := ComponentKernelEquality.exists_nonzero_distinguished_kernel_vector P H e C (k q₀).range
    z₀.val (hfull q₀ hq₀ z₀ hz₀)
  obtain ⟨t₀, ht₀⟩ := hv₀
  change k q₀ t₀ = v₀ at ht₀
  let L : V →ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec := {
    toFun := fun v => e.symm (C v P.distinguished).1
    map_add' := fun v w => by simp
    map_smul' := fun a v => by simp }
  let w := fun q => L (k q t₀)
  have hw : DifferentiableOn ℂ w U :=
    L.toContinuousLinearMap.differentiable.comp_differentiableOn
      (hk.clm_apply (differentiableOn_const t₀))
  have hw₀ : w q₀ = Geometry.ComplexBall.PrescribedSignsB.lineVector z₀.val := by
    change e.symm (C (k q₀ t₀) P.distinguished).1 = _
    rw [ht₀, he₀, LinearEquiv.symm_apply_apply]
  have hline (q : S) (hq : q ∈ U) (z : P.Domain)
      (hz : ∀ v : V, ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (C (k q v))) :
      w q ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val} := by
    have h := hz t₀ P.distinguished
    simp only [ite_true] at h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h.1
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    change a • Geometry.ComplexBall.PrescribedSignsB.lineVector z.val = e.symm (C (k q t₀) P.distinguished).1
    exact e.injective ((map_smul e a _).trans (ha.trans (e.apply_symm_apply _).symm))
  obtain ⟨O, period, hO, hqO, hOU, hperiod, heq⟩ :=
    HolomorphicLineCoordinate.exists_holomorphic_normalized_line_coordinate U hU w hw q₀ hq₀
      (hw₀ ▸ Geometry.ComplexBall.PrescribedSignsB.lineVector_ne_zero z₀.val) (by
        intro q hq
        obtain ⟨z, hz⟩ := hcover q hq
        exact ⟨z.val, hline q hq z hz⟩)
  refine ⟨O, period, hO, hqO, hOU, hperiod, ?_, ?_⟩
  · intro q hq
    obtain ⟨z, hz⟩ := hcover q (hOU hq)
    rw [heq q hq z.val (hline q (hOU hq) z hz)]
    exact z.property
  · intro q hq v
    obtain ⟨z, hz⟩ := hcover q (hOU hq)
    rw [heq q hq z.val (hline q (hOU hq) z hz)]
    exact hfull q (hOU hq) z hz v

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicCoefficientPatch
