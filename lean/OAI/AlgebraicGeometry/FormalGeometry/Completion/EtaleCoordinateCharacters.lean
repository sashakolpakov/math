import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Etale Coordinate Characters -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleCoordinateCharacters.Construction

noncomputable section

/-! The number of coordinate characters of a finite etale Hopf algebra
is at most the number of its geometric points. The bound follows from
linear independence and the actual split-etale algebra equivalence. -/

universe u
variable (K R : Type u) [Field K] [IsAlgClosed K] [CommRing R]
  [Algebra K R] [Module.Finite K R] [Algebra.Etale K R]

theorem etale_finrank_le_card_algHom : Module.finrank K R ≤ Nat.card (R →ₐ[K] K) := by
  classical
  have : Finite (R →ₐ[K] K) := (linearIndependent_algHom_toLinearMap K R K).finite
  have : IsArtinianRing R := isArtinian_of_tower K inferInstance
  let := Fintype.ofFinite (PrimeSpectrum R)
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K R
  let j : PrimeSpectrum R → (R →ₐ[K] K) := fun p =>
    (Pi.evalAlgHom K (fun _ : PrimeSpectrum R => K) p).comp e.toAlgHom
  have hj : Function.Injective j := by
    intro p q h
    by_contra hpq
    have hval := congrArg (fun f : R →ₐ[K] K => f (e.symm (Pi.single p 1))) h
    change e (e.symm (Pi.single p 1)) p = e (e.symm (Pi.single p 1)) q at hval
    rw [e.apply_symm_apply] at hval
    simp [Ne.symm hpq] at hval
  calc
    Module.finrank K R = Nat.card (PrimeSpectrum R) := by
      rw [e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
    _ ≤ Nat.card (R →ₐ[K] K) := Nat.card_le_card_of_injective j hj

variable [Coalgebra K R]

theorem etale_coordinateCharacters_card_le_points :
    Nat.card (GroupLike K R) ≤ Nat.card (R →ₐ[K] K) := by
  have : Finite (GroupLike K R) := (linearIndep_groupLikeVal (R := K) (A := R)).finite
  let := Fintype.ofFinite (GroupLike K R)
  have h : Nat.card (GroupLike K R) ≤ Module.finrank K R := by
    simpa only [Nat.card_eq_fintype_card] using
      (linearIndep_groupLikeVal (R := K) (A := R)).fintype_card_le_finrank
  exact h.trans (etale_finrank_le_card_algHom K R)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleCoordinateCharacters.Construction
