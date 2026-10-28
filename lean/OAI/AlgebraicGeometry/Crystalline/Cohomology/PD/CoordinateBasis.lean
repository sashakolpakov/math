import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi

/-! # Coordinate Basis -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CoordinateBasis.PDCoordinateBasis

noncomputable section

/-!
# A PD one-form basis from dual coordinate derivations

Coordinate derivations provide the coefficient functionals for the
coordinate differentials. Their Kronecker values and the expansion of
the universal derivation prove that these differentials are a basis.
-/

open Classical

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A] [Fintype σ]
  (I : Ideal A) (δ : DividedPowers I) (x : σ → A) (D : σ → Derivation R A A)
  (hpow : ∀ i n a, a ∈ I → D i (δ.dpow (n + 1) a) = δ.dpow n a • D i a)

def coefficient (i : σ) : DeRham.PDDeRham.Form R A I δ 1 →ₗ[A] A :=
  OneForms.PDOneForms.lift R A I δ A (D i) (fun n a ha => hpow i n a ha)

omit [Fintype σ] in
theorem coefficient_D (i : σ) (a : A) : coefficient R A σ I δ D hpow i (OneForms.PDOneForms.D R A I δ a) = D i a :=
  OneForms.PDOneForms.lift_D R A I δ A (D i) _ a

def toPi : DeRham.PDDeRham.Form R A I δ 1 →ₗ[A] (σ → A) :=
  LinearMap.pi (coefficient R A σ I δ D hpow)

omit [Fintype σ] in
theorem toPi_apply (ω : DeRham.PDDeRham.Form R A I δ 1) (i : σ) :
    toPi R A σ I δ D hpow ω i = coefficient R A σ I δ D hpow i ω := rfl

def fromPi : (σ → A) →ₗ[A] DeRham.PDDeRham.Form R A I δ 1 :=
  Fintype.linearCombination A (fun i => OneForms.PDOneForms.D R A I δ (x i))

theorem fromPi_apply (f : σ → A) : fromPi R A σ I δ x f =
    ∑ i, f i • OneForms.PDOneForms.D R A I δ (x i) := Fintype.linearCombination_apply _ _ _

variable (hD : ∀ a, OneForms.PDOneForms.D R A I δ a = ∑ i, D i a • OneForms.PDOneForms.D R A I δ (x i))

include hD in
theorem fromPi_toPi : (fromPi R A σ I δ x).comp (toPi R A σ I δ D hpow) = LinearMap.id := by
  apply OneForms.PDOneForms.linearMap_ext R A I δ (DeRham.PDDeRham.Form R A I δ 1)
  intro a
  change fromPi R A σ I δ x (toPi R A σ I δ D hpow (OneForms.PDOneForms.D R A I δ a)) =
    OneForms.PDOneForms.D R A I δ a
  rw [fromPi_apply]
  simp only [toPi_apply, coefficient_D]
  exact (hD a).symm

variable (hcoordinate : ∀ i j, D i (x j) = if j = i then (1 : A) else 0)

include hcoordinate in
theorem toPi_fromPi : (toPi R A σ I δ D hpow).comp (fromPi R A σ I δ x) = LinearMap.id := by
  classical
  apply (Pi.basisFun A σ).ext
  intro j
  change toPi R A σ I δ D hpow (fromPi R A σ I δ x (Pi.single j 1)) = Pi.single j 1
  rw [fromPi, Fintype.linearCombination_apply_single, one_smul]
  funext i
  rw [toPi_apply, coefficient_D, hcoordinate]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji, Ne.symm hji]

def formsEquiv : (σ → A) ≃ₗ[A] DeRham.PDDeRham.Form R A I δ 1 :=
  LinearEquiv.ofLinearMap (fromPi R A σ I δ x) (toPi R A σ I δ D hpow)
    (fromPi_toPi R A σ I δ x D hpow hD) (toPi_fromPi R A σ I δ x D hpow hcoordinate)

def basis : Module.Basis σ A (DeRham.PDDeRham.Form R A I δ 1) :=
  (Pi.basisFun A σ).map (formsEquiv R A σ I δ x D hpow hD hcoordinate)

theorem basis_apply (i : σ) : basis R A σ I δ x D hpow hD hcoordinate i = OneForms.PDOneForms.D R A I δ (x i) := by
  classical
  rw [basis, Module.Basis.map_apply]
  change fromPi R A σ I δ x (Pi.single i 1) = _
  rw [fromPi, Fintype.linearCombination_apply_single, one_smul]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CoordinateBasis.PDCoordinateBasis
