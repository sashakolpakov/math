import Mathlib.RingTheory.Ideal.Maps

/-! # Pointed Parameter Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PointedParameterTransport

noncomputable section

/-! Parameters defining a section remain parameters under an algebra
isomorphism preserving its evaluation map. -/

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (e : A ≃ₐ[R] B) (εA : A →ₐ[R] R) (εB : B →ₐ[R] R)
  (he : ∀ x, εB (e x) = εA x)

include he in
theorem kernel : (RingHom.ker εA.toRingHom).map e.toRingHom =
    RingHom.ker εB.toRingHom := by
  have h : RingHom.ker εA.toRingHom =
      (RingHom.ker εB.toRingHom).comap e.toRingHom := by
    ext x
    change εA x = 0 ↔ εB (e x) = 0
    rw [he]
  rw [h]
  exact Ideal.map_comap_of_surjective e.toRingHom e.surjective _

include he in
theorem span {ι : Type*} (a : ι → A)
    (ha : Ideal.span (Set.range a) = RingHom.ker εA.toRingHom) :
    Ideal.span (Set.range (fun i => e (a i))) = RingHom.ker εB.toRingHom := by
  have h := congrArg (Ideal.map e.toRingHom) ha
  rw [Ideal.map_span] at h
  rw [← Set.range_comp] at h
  exact h.trans (kernel e εA εB he)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PointedParameterTransport
