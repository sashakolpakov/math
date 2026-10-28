import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrimeCodimension

/-! # Principal Codimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalCodimension

noncomputable section

/-! A nonzero principal quotient on an integral affine support is
supported in at least one higher ambient codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

variable {R : Type} [CommRing R]

theorem mem_support (v w : PrimeSpectrum R) (r : R)
    (hw : w ∈ Module.support R (QuotSMulTop r (R ⧸ v.asIdeal))) :
    v.asIdeal ≤ w.asIdeal ∧ r ∈ w.asIdeal := by
  rw [Module.support_quotSMulTop] at hw
  have hle := hw.1
  simp only [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker,
    PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at hle
  exact ⟨hle, hw.2 (Set.mem_singleton r)⟩

theorem bound (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (v : PrimeSpectrum R) (hv : V.supportCodimension (FiltrationAvoidance.support j v) = k)
    (r : R) (hr : r ∉ v.asIdeal)
    (w : PrimeSpectrum R) (hw : w ∈ Module.support R (QuotSMulTop r (R ⧸ v.asIdeal))) :
    k + 1 ≤ V.supportCodimension (FiltrationAvoidance.support j w) := by
  obtain ⟨hvw, hrw⟩ := mem_support v w r hw
  have hne : w ≠ v := fun he => hr (he ▸ hrw)
  have hs : FiltrationAvoidance.support j w < FiltrationAvoidance.support j v :=
    lt_of_le_of_ne (PrimeCodimension.antitone j v w hvw)
      (fun he => hne (PrimeCodimension.injective j he))
  have h := Supports.codimension_strictAnti V m hs
  rw [hv] at h
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalCodimension
