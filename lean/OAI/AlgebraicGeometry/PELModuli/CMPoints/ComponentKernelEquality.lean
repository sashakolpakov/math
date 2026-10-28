import OAI.AlgebraicGeometry.PELModuli.CMPoints.ClosedCoefficientPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine

/-! # Component Kernel Equality -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentKernelEquality

noncomputable section

section

/-! A distinguished Hermitian normalizer transports the literal
reference period subspace to the coefficient-period conditions. -/

open scoped Classical

def conjugateVecEquiv (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec where
  toFun x := star (e (star x))
  invFun x := star (e.symm (star x))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' a x := by simp

def componentNormalizer {s : ℕ} (d : Fin s) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
  LinearEquiv.piCongrRight (fun i =>
    if i = d then e.prodCongr (conjugateVecEquiv e) else LinearEquiv.refl ℂ _)

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

omit [NumberField E] [NumberField.IsCMField E] in
theorem componentNormalizer_prescribed
    (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) (componentNormalizer P.distinguished e u) ↔
      Geometry.ComplexBall.PrescribedSignsB.Prescribed (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]))
        P.distinguished P.compactSigns z u := by
  unfold ClosedCoefficientPeriods.componentPrescribed Geometry.ComplexBall.PrescribedSignsB.Prescribed
  apply forall_congr'
  intro i
  by_cases hi : i = P.distinguished
  · subst i
    simp only [componentNormalizer, LinearEquiv.piCongrRight_apply, ite_true]
    change (e (u P.distinguished).1 ∈ Submodule.span ℂ {e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)} ∧
      Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings H P.distinguished (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z))
        (star (e (star (u P.distinguished).2))) = 0) ↔ _
    have hb := he (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (u P.distinguished).2)
    have hb' : Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings H P.distinguished (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z))
        (star (e (star (u P.distinguished).2))) =
      Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]) P.distinguished
        (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (u P.distinguished).2 := by
      simpa [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian, Geometry.ComplexBall.PrescribedSignsB.localB, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ] using hb
    rw [hb']
    apply and_congr _ Iff.rfl
    rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, e.injective ((map_smul e a _).trans ha)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (map_smul e a _).symm.trans (congrArg e ha)⟩
  · simp [hi, componentNormalizer, LinearEquiv.piCongrRight_apply]

theorem referencePeriod_finrank (hP : P.IsAdmissible) (z : P.Domain) :
    Module.finrank ℂ (P.periodFamily z) = 3 * s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hhol, _⟩ := hP
  obtain ⟨O, _, hz, _, e, _, he⟩ := hhol z z.property
  obtain ⟨hlin, hspan⟩ := he z hz
  rw [← hspan]
  simpa only [Fintype.card_fin] using finrank_span_eq_card hlin

theorem componentPrescribed_iff_mem_normalized_reference
    (hP : P.IsAdmissible) (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (z : P.Domain) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) u ↔
      u ∈ (P.periodFamily z).map (componentNormalizer P.distinguished e).toLinearMap := by
  obtain ⟨v, rfl⟩ := (componentNormalizer P.distinguished e).surjective u
  rw [componentNormalizer_prescribed P H e he, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfiber⟩ := hP
  exact ((hfiber z z.property).1 v).symm

end

/-! The native half-dimensional kernel is exactly the coefficient
subspace once all its vectors satisfy the prescribed equations. -/

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  {V : Type} [AddCommGroup V] [Module ℂ V]

include hP in
theorem component_kernel_equality_of_inclusion
    (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (C : V ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (K : Submodule ℂ V)
    (hdim : Module.finrank ℂ K = 3 * s) (z : P.Domain)
    (hK : ∀ v ∈ K, ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (C v)) :
    ∀ v : V, v ∈ K ↔ ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (C v) := by
  let S := (P.periodFamily z).map (componentNormalizer P.distinguished e).toLinearMap
  have hle : K.map C.toLinearMap ≤ S := by
    rintro _ ⟨v, hv, rfl⟩
    exact (componentPrescribed_iff_mem_normalized_reference P hP H e he z _).mp (hK v hv)
  have hdim' : Module.finrank ℂ (K.map C.toLinearMap) = Module.finrank ℂ S := by
    rw [C.finrank_map_eq, hdim, (componentNormalizer P.distinguished e).finrank_map_eq,
      referencePeriod_finrank P hP]
  have heq : K.map C.toLinearMap = S := Submodule.eq_of_le_of_finrank_eq hle hdim'
  intro v
  rw [componentPrescribed_iff_mem_normalized_reference P hP H e he]
  change v ∈ K ↔ C v ∈ S
  rw [← heq, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

omit [NumberField E] [NumberField.IsCMField E] in
theorem exists_nonzero_distinguished_kernel_vector
    (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (C : V ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (K : Submodule ℂ V) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hK : ∀ v : V, v ∈ K ↔ ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) (C v)) :
    ∃ v ∈ K, (C v P.distinguished).1 = e (Geometry.ComplexBall.PrescribedSignsB.lineVector z) := by
  let u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) := fun i => if i = P.distinguished then (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z), 0) else 0
  have hu : ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) u := by
    intro i
    by_cases hi : i = P.distinguished
    · subst i
      simp [u, Submodule.mem_span_singleton_self, Geometry.ComplexBall.PrescribedSignsB.localB]
    · simp [u, hi]
  refine ⟨C.symm u, (hK _).mpr ?_, ?_⟩
  · simpa only [C.apply_symm_apply] using hu
  · simp [u]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentKernelEquality
