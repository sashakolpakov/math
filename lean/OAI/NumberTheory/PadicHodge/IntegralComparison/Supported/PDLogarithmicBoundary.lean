import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDLiftIndependence

/-! # PD Logarithmic Boundary -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDLogarithmicBoundary.Complex

noncomputable section

/-! A fixed finite PD logarithm gives an actual cochain boundary for
changing residual parameter lifts. The primitive lies in bidegree
`(g - 1, g)` and its differential has no extra total-complex sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open _root_.Complex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X)
  (n : ℕ) (a b : Fin (n + 1) → Q.thickening.ring)
  (hab : ∀ i, Q.thickening.reduction (b i) = Q.thickening.reduction (a i))

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex.topFrame p k X Q (n + 1) a

def primitiveForm (N : ℕ) :
    ((PDComplex.localizedComplex p k X Q).X n).obj (op (PDComplex.topCoefficient p k X Q (n + 1) a)) :=
  PD.LogarithmicHomotopy.Forms.logarithmicPrimitive (WittVector p k) (T).thickening.ring
    (RingHom.ker (T).thickening.reduction) (T).thickening.dividedPowers N n
    (PDComplex.coordinateUnit p k X Q (n + 1) a) (PDLiftIndependence.Complex.changedCoordinateUnit p k X Q (n + 1) a b hab)

theorem primitiveForm_differential (N : ℕ) (hN : (N.factorial : (T).thickening.ring) = 0) :
    ((PDComplex.localizedComplex p k X Q).d n (n + 1)).app (op (PDComplex.topCoefficient p k X Q (n + 1) a))
        (primitiveForm p k X Q n a b hab N) =
      PDLiftIndependence.Complex.changedLogarithmicForm p k X Q (n + 1) a b hab - PDComplex.logarithmicForm p k X Q (n + 1) a := by
  rw [PDComplex.localizedComplex_d]
  apply (PD.LogarithmicHomotopy.Forms.logarithmicPrimitive_differential (WittVector p k)
    (T).thickening.ring (RingHom.ker (T).thickening.reduction) (T).thickening.dividedPowers N hN n
    (PDComplex.coordinateUnit p k X Q (n + 1) a) (PDLiftIndependence.Complex.changedCoordinateUnit p k X Q (n + 1) a b hab) ?_).symm
  intro i
  rw [PDLiftIndependence.Complex.changedCoordinateUnit_val, PDComplex.coordinateUnit_val]
  exact PDLiftIndependence.Complex.coordinate_difference p k X Q (n + 1) a b hab i

def boundaryCochain (N : ℕ) : (PDComplex.total p k X Q (n + 1) a).X (n + (n + 1)) :=
  AugmentedOrdered.CechTopTotal.topTotalInclusion (PDComplex.family p k X Q (n + 1) a)
    (PDComplex.localizedComplex p k X Q) (n + 1) (by simp) n (n + (n + 1)) rfl
    (primitiveForm p k X Q n a b hab N)

theorem boundaryCochain_differential (N : ℕ) (hN : (N.factorial : (T).thickening.ring) = 0) :
    (PDComplex.total p k X Q (n + 1) a).d (n + (n + 1)) ((n + 1) + (n + 1))
        (boundaryCochain p k X Q n a b hab N) =
      AugmentedOrdered.CechTopTotal.topTotalInclusion (PDComplex.family p k X Q (n + 1) a)
        (PDComplex.localizedComplex p k X Q) (n + 1) (by simp) (n + 1) ((n + 1) + (n + 1)) rfl
        (PDLiftIndependence.Complex.changedLogarithmicForm p k X Q (n + 1) a b hab) -
      AugmentedOrdered.CechTopTotal.topTotalInclusion (PDComplex.family p k X Q (n + 1) a)
        (PDComplex.localizedComplex p k X Q) (n + 1) (by simp) (n + 1) ((n + 1) + (n + 1)) rfl
        (PDComplex.logarithmicForm p k X Q (n + 1) a) := by
  have h := AugmentedOrdered.CechTopTotal.topTotalInclusion_differential
    (PDComplex.family p k X Q (n + 1) a) (PDComplex.localizedComplex p k X Q) (n + 1) (by simp)
    n (n + (n + 1)) ((n + 1) + (n + 1)) rfl (by omega)
    (primitiveForm p k X Q n a b hab N)
  let j := AugmentedOrdered.CechTopTotal.topTotalInclusion (PDComplex.family p k X Q (n + 1) a)
    (PDComplex.localizedComplex p k X Q) (n + 1) (by simp) (n + 1) ((n + 1) + (n + 1)) rfl
  have hp := congrArg (fun z : ((PDComplex.localizedComplex p k X Q).X (n + 1)).obj
    (op (PDComplex.topCoefficient p k X Q (n + 1) a)) => j z)
    (primitiveForm_differential p k X Q n a b hab N hN)
  exact h.trans (hp.trans (j.hom.map_sub _ _))

theorem factorial_zero_of_prime_power (r : ℕ) (hr : (p : Q.thickening.ring) ^ r = 0) :
    ((r * p).factorial : (T).thickening.ring) = 0 := by
  have ht : (p : (T).thickening.ring) ^ r = 0 := by
    have h := congrArg
      (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (PDComplex.topCoefficient p k X Q (n + 1) a)).ambientMap hr
    simpa only [map_pow, map_natCast, map_zero] using h
  obtain ⟨d, hd⟩ := DividedPower.Nilpotence.pow_dvd_mul_factorial p r (Fact.out : p.Prime).pos
  rw [hd, Nat.cast_mul, Nat.cast_pow, ht, zero_mul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDLogarithmicBoundary.Complex
