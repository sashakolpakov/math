import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoordinateJacobian
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementSign

/-! # Differential Transition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DifferentialTransition

noncomputable section

/-! Projective changes of differential coordinates, including the ordering
sign, for arbitrary derivations and modules over the base ring. -/

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoordinateJacobian

universe u v w
variable {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
  {n : ℕ}

def frame (v : Fin n → M) (k : Fin n) (u : Sˣ) (x : Fin n → S) (j : Fin n) : M :=
  if j = k then -((u⁻¹ : Sˣ) : S) ^ 2 • v k
  else ((u⁻¹ : Sˣ) : S) • v j - (((u⁻¹ : Sˣ) : S) ^ 2 * x j) • v k

theorem wedge_frame (v : Fin n → M) (k : Fin n) (u : Sˣ) (x : Fin n → S) :
    exteriorPower.ιMulti S n (frame v k u x) =
      (-((u⁻¹ : Sˣ) : S) ^ (n + 1)) • exteriorPower.ιMulti S n v := by
  let b := Pi.basisFun S (Fin n)
  let L := b.constr S v
  have hL (j : Fin n) : L (b j) = v j := b.constr_basis S v j
  have h := congrArg (exteriorPower.map n L)
    (CoordinateJacobian.wedge_frame b k u x)
  rw [map_smul, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti] at h
  convert h using 1
  · congr 1
    funext j
    simp only [frame, CoordinateJacobian.frame, Function.comp_apply]
    split_ifs <;> simp only [map_smul, map_sub, hL]
  · congr 1
    congr 1
    funext j
    exact (b.constr_basis S v j).symm

variable {R : Type w} [CommRing R] [Algebra R S] [Module R M] [IsScalarTower R S M]

omit [IsScalarTower R S M] in
theorem wedge_differential_coordinates (D : Derivation R S M) (k : Fin n) (u : Sˣ)
    (x : Fin n → S) (hk : x k = (u : S)) :
    exteriorPower.ιMulti S n (fun j => D (CoordinateJacobian.coordinates k u x j)) =
      (-((u⁻¹ : Sˣ) : S) ^ (n + 1)) • exteriorPower.ιMulti S n (fun j => D (x j)) := by
  have hi : D ((u⁻¹ : Sˣ) : S) = -((u⁻¹ : Sˣ) : S) ^ 2 • D (x k) := by
    rw [D.leibniz_of_mul_eq_one (Units.inv_mul u), hk]
  have he : (fun j => D (CoordinateJacobian.coordinates k u x j)) = frame (fun j => D (x j)) k u x := by
    funext j
    by_cases hj : j = k
    · simp only [CoordinateJacobian.coordinates, frame, ite_eq_left hj]
      exact hi
    · simp [CoordinateJacobian.coordinates, frame, hj, D.leibniz, hi, sub_eq_add_neg, smul_smul, mul_comm, add_comm]
  rw [he, wedge_frame]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DifferentialTransition
