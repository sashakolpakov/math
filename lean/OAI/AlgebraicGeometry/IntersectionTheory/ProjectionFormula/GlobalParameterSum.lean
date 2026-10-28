import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeOrder

/-! # Global Parameter Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum

noncomputable section

section

/-! Local parameter orders define weights on global supports,
with zero weight when the parameter vanishes identically there. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Weights

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable (Z : Scheme) (x : Z) (r : Z.presheaf.stalk x)

def weight (C : IrreducibleCloseds Z) : ℚ :=
  if hx : x ∈ (C : Set Z) then
    if Local.Principal.supportStalkMap Z C x hx r ≠ 0 then
      ((Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme C).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx))
        (Local.Principal.supportStalkMap Z C x hx r)).toNat : ℚ)
    else 0
  else 0

theorem primeClosure_injective : Function.Injective (Stalk.DivisorSupport.primeClosure Z x) := by
  intro p q hpq
  apply (Z.fromSpecStalk x).isEmbedding.injective
  exact (Stalk.DivisorSupport.primeClosure_point Z x p).symm.trans
    ((congrArg CycleClass.Thom.IntersectionGeometry.supportPoint hpq).trans (Stalk.DivisorSupport.primeClosure_point Z x q))

theorem primeClosure_kernel (C : IrreducibleCloseds Z) (hx : x ∈ (C : Set Z)) :
    Stalk.DivisorSupport.primeClosure Z x (Stalk.PrimeQuotient.kernelPrime Z C x hx) = C := by
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint (Stalk.DivisorSupport.primeClosure Z x (Stalk.PrimeQuotient.kernelPrime Z C x hx)) = CycleClass.Thom.IntersectionGeometry.supportPoint C
  rw [Stalk.DivisorSupport.primeClosure_point, Stalk.PrimeQuotient.kernelPrime_image]

theorem prime_weight (p : PrimeSpectrum (Z.presheaf.stalk x)) :
    weight Z x r (Stalk.DivisorSupport.primeClosure Z x p) =
      if r ∉ p.asIdeal then
        ((Ring.ord ((Z.presheaf.stalk x) ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ)
      else 0 := by
  rw [weight, dite_eq_left (Stalk.DivisorSupport.point_mem_primeClosure Z x p)]
  by_cases hp : r ∉ p.asIdeal
  · rw [ite_eq_left hp, ite_eq_left (Stalk.PrimeOrder.image_ne_zero Z x p r hp),
      Stalk.PrimeOrder.quotient_order]
  · have hz : Local.Principal.supportStalkMap Z (Stalk.DivisorSupport.primeClosure Z x p) x (Stalk.DivisorSupport.point_mem_primeClosure Z x p) r = 0 := by
      apply RingHom.mem_ker.mp
      rw [Stalk.PrimeQuotient.kernel_eq Z (Stalk.DivisorSupport.primeClosure Z x p) x
        (Stalk.DivisorSupport.point_mem_primeClosure Z x p) p (Stalk.DivisorSupport.primeClosure_point Z x p).symm]
      exact not_not.mp hp
    rw [ite_eq_right hp, ite_eq_right (not_ne_iff.mpr hz)]

theorem closed_weight (hr : r ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk x)) :
    weight Z x r (Stalk.DivisorSupport.primeClosure Z x (IsLocalRing.closedPoint (Z.presheaf.stalk x))) = 0 := by
  rw [prime_weight]
  exact ite_eq_right (show ¬r ∉ (IsLocalRing.closedPoint (Z.presheaf.stalk x)).asIdeal from not_not.mpr hr)

end Weights

end

/-! A finite local specialization sum can be rewritten over a
single fixed finite collection of global components. Extra global
components have zero contribution at the chosen endpoint point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum.Weights

theorem reindex (Z : Scheme) (x : Z) (r : Z.presheaf.stalk x)
    (hr : r ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk x))
    (c : IrreducibleCloseds Z → ℚ) (F : Finset (IrreducibleCloseds Z))
    (T : Finset (PrimeSpectrum (Z.presheaf.stalk x)))
    (hT : ∀ p ∈ T, Stalk.DivisorSupport.primeClosure Z x p ∈ F ∧ r ∉ p.asIdeal)
    (hout : ∀ p, p ≠ IsLocalRing.closedPoint (Z.presheaf.stalk x) → p ∉ T → c (Stalk.DivisorSupport.primeClosure Z x p) = 0) :
    (∑ p ∈ T, c (Stalk.DivisorSupport.primeClosure Z x p) *
      ((Ring.ord ((Z.presheaf.stalk x) ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ)) =
      ∑ C ∈ F, c C * Weights.weight Z x r C := by
  have hsub : T.image (Stalk.DivisorSupport.primeClosure Z x) ⊆ F := by
    rintro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    exact (hT p hp).1
  have hz (C : IrreducibleCloseds Z) (_ : C ∈ F) (hC : C ∉ T.image (Stalk.DivisorSupport.primeClosure Z x)) :
      c C * Weights.weight Z x r C = 0 := by
    by_cases hx : x ∈ (C : Set Z)
    · let p := Stalk.PrimeQuotient.kernelPrime Z C x hx
      have hpC : Stalk.DivisorSupport.primeClosure Z x p = C := Weights.primeClosure_kernel Z x C hx
      by_cases hp : p = IsLocalRing.closedPoint (Z.presheaf.stalk x)
      · rw [← hpC, hp, Weights.closed_weight Z x r hr, mul_zero]
      · have hpT : p ∉ T := fun hpT => hC (Finset.mem_image.mpr ⟨p, hpT, hpC⟩)
        have hc : c C = 0 := hpC ▸ hout p hp hpT
        rw [hc, zero_mul]
    · rw [Weights.weight, dite_eq_right hx, mul_zero]
  calc
    _ = ∑ p ∈ T, c (Stalk.DivisorSupport.primeClosure Z x p) * Weights.weight Z x r (Stalk.DivisorSupport.primeClosure Z x p) :=
      Finset.sum_congr rfl (fun p hp => by rw [Weights.prime_weight, ite_eq_left (hT p hp).2])
    _ = ∑ C ∈ T.image (Stalk.DivisorSupport.primeClosure Z x), c C * Weights.weight Z x r C := by
      rw [Finset.sum_image]
      · rfl
      · exact fun p _ q _ hpq => Weights.primeClosure_injective Z x hpq
    _ = _ := Finset.sum_subset hsub hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum
