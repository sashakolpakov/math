import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLiftIdeal

/-! # Divided Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLift.Comparison

noncomputable section

/-!
# IntegralComparison: the divided-coordinate lift recovers any compatible étale chart map
-/

universe u

variable (R σ C T : Type u) [CommRing R] [CommRing C] [CommRing T]
  [Algebra R C] [Algebra (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) C]
  [Algebra R T] [Algebra.Etale (MvPolynomial σ R) C]
  (I : Ideal T) (p : ℕ) [Fact p.Prime] (δ : DividedPowers I)
  (hp : IsNilpotent (p : T)) (l : C →ₐ[R] T)

attribute [local instance] DividedCoordinateLift.scalarAlgebra DividedCoordinateLift.scalarTower

variable (A : Type u) [CommRing A] [Algebra R A] (K : Ideal A) (ε : DividedPowers K)
  (a : T →ₐ[R] A) (b : C →ₐ[R] A) (g : DividedPowerAlgebra T (σ →₀ T) →ₐ[R] A)
  (hg : DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers T σ I δ) ε g.toRingHom)
  (hbase : ∀ t, g (algebraMap T (DividedPowerAlgebra T (σ →₀ T)) t) = a t)
  (hcoord : ∀ i, g (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ 1 i) =
    b (algebraMap (MvPolynomial σ R) C (MvPolynomial.X i)) -
      a (l (algebraMap (MvPolynomial σ R) C (MvPolynomial.X i))))
  (hclosed : ∀ c, b c - a (l c) ∈ K)

local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra T (σ →₀ T)
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateLift.lift R σ C T I p δ hp l

include hg hbase hcoord hclosed in
theorem comparison : g.comp e = b := by
  have hpA : IsNilpotent (p : A) := by
    simpa only [map_natCast] using hp.map a.toRingHom
  apply CoordinateLifting.lift_unique R σ C A (A ⧸ K) (Ideal.Quotient.mkₐ R K)
    (fun x h => DividedPower.Nilpotence.nilpotent_of_mem ε p (Fact.out : p.Prime).pos hpA
      (Ideal.Quotient.eq_zero_iff_mem.mp h)) (g.comp e) b
  · apply AlgHom.ext
    intro c
    apply Ideal.Quotient.eq.mpr
    have hm : g (e c - algebraMap T G (l c)) ∈ K :=
      hg.ideal_comp (Ideal.mem_map_of_mem g.toRingHom
        (DividedLiftIdeal.difference_mem R σ C T I p δ hp l c))
    rw [map_sub, hbase] at hm
    have hs := K.sub_mem hm (hclosed c)
    have he : (g (e c) - a (l c)) - (b c - a (l c)) = g (e c) - b c := by abel
    exact he ▸ hs
  · intro i
    change g (e (algebraMap P C (MvPolynomial.X i))) = b (algebraMap P C (MvPolynomial.X i))
    rw [DividedCoordinateLift.lift_coordinate, DividedCoordinateLift.coordinates,
      map_add, hbase, hcoord]
    abel

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLift.Comparison
