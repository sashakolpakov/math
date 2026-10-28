import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedAlgebraMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLift

/-! # Divided Universal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedUniversal

noncomputable section

/-!
# IntegralComparison: the universal PD extension of two compatible étale chart maps
-/

universe u

variable (R σ C T : Type u) [CommRing R] [CommRing C] [CommRing T]
  [Algebra R C] [Algebra (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) C]
  [Algebra R T] [Algebra.Etale (MvPolynomial σ R) C]
  (I : Ideal T) (p : ℕ) [Fact p.Prime] (δ : DividedPowers I)
  (hp : IsNilpotent (p : T)) (l : C →ₐ[R] T)
  (A : Type u) [CommRing A] [Algebra R A] (K : Ideal A) (ε : DividedPowers K)
  (a : T →ₐ[R] A) (ha : DividedPowers.IsDPMorphism δ ε a.toRingHom)
  (b : C →ₐ[R] A) (hclosed : ∀ c, b c - a (l c) ∈ K)

attribute [local instance] DividedCoordinateLift.scalarAlgebra
  DividedCoordinateLift.scalarTower

local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra T (σ →₀ T)
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateLift.lift R σ C T I p δ hp l
local notation "x" => fun i => b (algebraMap P C (MvPolynomial.X i)) - a (l (algebraMap P C (MvPolynomial.X i)))
local notation "hx" => fun i => hclosed (algebraMap P C (MvPolynomial.X i))

def lift : G →ₐ[R] A := Free.DividedAlgebraMap.lift R T A σ a K ε x hx

omit [IsScalarTower R (MvPolynomial σ R) C] [Algebra.Etale (MvPolynomial σ R) C] in
theorem lift_coefficient (t : T) :
    lift R σ C T l A K ε a b hclosed (algebraMap T G t) = a t :=
  Free.DividedAlgebraMap.lift_coefficient R T A σ a K ε x hx t

omit [IsScalarTower R (MvPolynomial σ R) C] [Algebra.Etale (MvPolynomial σ R) C] in
theorem lift_coordinate (i : σ) :
    lift R σ C T l A K ε a b hclosed (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ 1 i) = x i :=
  Free.DividedAlgebraMap.lift_coordinate R T A σ a K ε x hx i

omit [IsScalarTower R (MvPolynomial σ R) C] [Algebra.Etale (MvPolynomial σ R) C] in
include ha in
theorem lift_isDPMorphism : DividedPowers.IsDPMorphism
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers T σ I δ) ε
    (lift R σ C T l A K ε a b hclosed).toRingHom :=
  Free.DividedAlgebraMap.lift_isDPMorphism R T A σ a K ε x hx I δ ha

include ha in
theorem lift_chart : (lift R σ C T l A K ε a b hclosed).comp e = b :=
  DividedLift.Comparison.comparison R σ C T I p δ hp l A K ε a b
    (lift R σ C T l A K ε a b hclosed)
    (lift_isDPMorphism R σ C T I δ l A K ε a ha b hclosed)
    (lift_coefficient R σ C T l A K ε a b hclosed)
    (lift_coordinate R σ C T l A K ε a b hclosed) hclosed

theorem lift_unique (g : G →ₐ[R] A)
    (hg : DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers T σ I δ) ε g.toRingHom)
    (hbase : ∀ t, g (algebraMap T G t) = a t)
    (hchart : g.comp e = b) : g = lift R σ C T l A K ε a b hclosed := by
  apply Free.DividedAlgebraMap.lift_unique R T A σ a K ε x hx I δ g hg hbase
  intro i
  have he := AlgHom.congr_fun hchart (algebraMap P C (MvPolynomial.X i))
  change g (e (algebraMap P C (MvPolynomial.X i))) = _ at he
  rw [DividedCoordinateLift.lift_coordinate, DividedCoordinateLift.coordinates,
    map_add, hbase] at he
  exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans he)

include ha hclosed in
theorem existsUnique_lift : ∃! g : G →ₐ[R] A,
    DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers T σ I δ) ε g.toRingHom ∧
    (∀ t, g (algebraMap T G t) = a t) ∧ g.comp e = b := by
  refine ⟨lift R σ C T l A K ε a b hclosed,
    ⟨lift_isDPMorphism R σ C T I δ l A K ε a ha b hclosed,
      lift_coefficient R σ C T l A K ε a b hclosed,
      lift_chart R σ C T I p δ hp l A K ε a ha b hclosed⟩, ?_⟩
  intro g hg
  exact lift_unique R σ C T I p δ hp l A K ε a b hclosed g hg.1 hg.2.1 hg.2.2

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedUniversal
