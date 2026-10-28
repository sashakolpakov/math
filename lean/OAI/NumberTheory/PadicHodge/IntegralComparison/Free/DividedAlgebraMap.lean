import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal

/-! # Divided Algebra Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedAlgebraMap

noncomputable section

/-!
# IntegralComparison: native free PD algebra maps retain the original coefficient algebra
-/

universe u

variable (R T A σ : Type u) [CommRing R] [CommRing T] [CommRing A]
  [Algebra R T] [Algebra R A] (a : T →ₐ[R] A)
  (K : Ideal A) (ε : DividedPowers K) (x : σ → A) (hx : ∀ i, x i ∈ K)

local notation "G" => DividedPowerAlgebra T (σ →₀ T)

def lift : G →ₐ[R] A := by
  letI : Algebra T A := a.toRingHom.toAlgebra
  letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  exact (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal.FreeRelativeUniversal.lift T σ A K ε x hx).restrictScalars R

theorem lift_coefficient (t : T) : lift R T A σ a K ε x hx (algebraMap T G t) = a t := by
  let : Algebra T A := a.toRingHom.toAlgebra
  exact (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal.FreeRelativeUniversal.lift T σ A K ε x hx).commutes t

theorem lift_coordinate (i : σ) : lift R T A σ a K ε x hx (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ 1 i) = x i := by
  let : Algebra T A := a.toRingHom.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal.FreeRelativeUniversal.lift_coordinate T σ A K ε x hx i

theorem lift_isDPMorphism (I : Ideal T) (δ : DividedPowers I)
    (ha : DividedPowers.IsDPMorphism δ ε a.toRingHom) :
    DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers T σ I δ) ε (lift R T A σ a K ε x hx).toRingHom := by
  let : Algebra T A := a.toRingHom.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal.FreeRelativeUniversal.lift_isDPMorphism T σ I δ A K ε ha x hx

theorem lift_unique (I : Ideal T) (δ : DividedPowers I) (f : G →ₐ[R] A)
    (hf : DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers T σ I δ) ε f.toRingHom)
    (hbase : ∀ t, f (algebraMap T G t) = a t)
    (hcoord : ∀ i, f (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ 1 i) = x i) : f = lift R T A σ a K ε x hx := by
  let : Algebra T A := a.toRingHom.toAlgebra
  let fT : G →ₐ[T] A := { f.toRingHom with commutes' := hbase }
  have he := AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal.FreeRelativeUniversal.lift_unique T σ I δ A K ε x hx fT hf hcoord
  exact AlgHom.ext (fun z => AlgHom.congr_fun he z)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedAlgebraMap
