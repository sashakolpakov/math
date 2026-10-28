import Mathlib.Topology.Algebra.Ring.Basic

/-! # Dense Integral Subrings -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseIntegralSubrings.TestTransport

noncomputable section

/-! Continuous ring maps preserve closed integral subrings when the
ordinary integers are dense in the source integral subring. -/

variable {K L : Type*} [CommRing K] [CommRing L]
  [TopologicalSpace K] [TopologicalSpace L]

theorem ringHom_mem_of_dense_integers (f : K →+* L) (hf : Continuous f)
    (A : Subring K) (B : Subring L) (hA : DenseRange (fun n : ℤ => (n : A)))
    (hB : IsClosed (B : Set L)) {x : K} (hx : x ∈ A) : f x ∈ B := by
  apply hA.induction_on (p := fun a : A => f a.val ∈ B) ⟨x, hx⟩
    (hB.preimage (hf.comp continuous_subtype_val))
  intro n
  change f (n : K) ∈ B
  rw [map_intCast]
  exact intCast_mem B n

theorem ringEquiv_integral_iff_of_dense_integers (e : K ≃+* L)
    (he : Continuous e) (hi : Continuous e.symm)
    (A : Subring K) (B : Subring L)
    (hA : DenseRange (fun n : ℤ => (n : A)))
    (hB : DenseRange (fun n : ℤ => (n : B)))
    (hAc : IsClosed (A : Set K)) (hBc : IsClosed (B : Set L)) (y : L) :
    y ∈ B ↔ e.symm y ∈ A := by
  constructor
  · exact ringHom_mem_of_dense_integers e.symm.toRingHom hi B A hB hAc
  · intro hy
    have h := ringHom_mem_of_dense_integers e.toRingHom he A B hA hBc hy
    change e (e.symm y) ∈ B at h
    simpa only [RingEquiv.apply_symm_apply] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseIntegralSubrings.TestTransport
