import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Flat

/-! # Algebra Equiv Regular Sequence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivRegularSequence

noncomputable section

/-! Actual weakly regular sequences are preserved by a ring
isomorphism, through its genuine flat algebra structure. -/
variable {A B : Type*} [CommRing A] [CommRing B]

theorem regular (e : A ≃+* B) {n : ℕ} (s : Fin n → A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn s)) :
    RingTheory.Sequence.IsWeaklyRegular B (List.ofFn (fun i => e (s i))) := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module.Flat A B := RingHom.Flat.of_bijective e.bijective
  have h := hs.of_flat (S := B)
  have he : (List.ofFn s).map (algebraMap A B) = List.ofFn (fun i => e (s i)) := by
    rw [List.map_ofFn]
    rfl
  rw [he] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivRegularSequence
