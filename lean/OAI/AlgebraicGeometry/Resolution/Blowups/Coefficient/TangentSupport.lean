import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion

/-! # Tangent Support -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentSupport.Construction

noncomputable section

/-! Every prime containing a coefficient tangent center contains the original tangent ideal. -/

universe u

theorem relative_tangent_le_of_coefficient_tangent_center_le_prime
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (z : R) (J : Ideal R) (n m : ℕ) (q : Ideal R) [q.IsPrime]
    (hq : TangentNaturality.Construction.coefficientTangentCenter k z J (n + 1) m ≤ q) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ q := by
  let C := Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1)
  let i : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hterm := le_iSup (fun j : Fin (n + 1) =>
    ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
      WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) j) i
  change ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
    WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) i ≤ C at hterm
  have hC : C ≤ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C m :=
    UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k C (Nat.zero_le m)
  intro x hx
  have hp : x ^ WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) i ∈ TangentNaturality.Construction.coefficientTangentCenter k z J (n + 1) m := by
    change Ideal.Quotient.mk (Ideal.span {z}) (x ^ WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) i) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C m
    rw [map_pow]
    exact hC (hterm (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hx) _))
  exact (inferInstance : q.IsPrime).isRadical ⟨WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) i, hq hp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentSupport.Construction
