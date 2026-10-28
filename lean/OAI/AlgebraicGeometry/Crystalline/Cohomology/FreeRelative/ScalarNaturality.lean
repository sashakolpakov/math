import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.ScalarComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.RelativeScalarMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormTranslations

/-! # Scalar Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.ScalarNaturality.FreeRelativeScalarNaturality

noncomputable section

/-! # Coordinate comparison respects actual relative PD affine maps -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (W R S σ : Type u) [CommRing W] [CommRing R] [CommRing S]
  [Algebra W R] [Algebra W S] [Fintype σ] [LinearOrder σ]
  (I : Ideal R) (δ : DividedPowers I) (J : Ideal S) (ε : DividedPowers J)
  (φ : R →+* S) (hW : ∀ w, φ (algebraMap W R w) = algebraMap W S w)
  (f : DividedPowerAlgebra R (σ →₀ R) →ₐ[W] DividedPowerAlgebra S (σ →₀ S))
  (h : ∀ r, f (algebraMap R (DividedPowerAlgebra R (σ →₀ R)) r) =
    algebraMap S (DividedPowerAlgebra S (σ →₀ S)) (φ r))
  (hf : DividedPowers.IsDPMorphism (Powers.FreeRelativePowers.dividedPowers R σ I δ)
    (Powers.FreeRelativePowers.dividedPowers S σ J ε) f.toRingHom)
  (b : σ → S) (hX : ∀ i, f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) =
    algebraMap S (DividedPowerAlgebra S (σ →₀ S)) (b i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i)

local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "IR" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "IS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal S σ J
local notation "γR" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
local notation "γS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers S σ J ε

include hX in
theorem component (n : ℕ) :
    (((PD.RelativeScalarMap.PDRelativeScalarMap.complexMap W R S GR GS φ hW f.toRingHom h IR γR IS γS hf).f n).hom.comp
      ((ScalarComparison.FreeRelativeScalarComparison.complexIso W R σ I δ).hom.f n).hom) =
    (((ScalarComparison.FreeRelativeScalarComparison.complexIso W S σ J ε).hom.f n).hom.comp
      (TensorProduct.map f.toLinearMap (LinearMap.id : (⋀[W]^n (σ →₀ W)) →ₗ[W] _))) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext_on (ExteriorCoordinate.ExteriorCoordinateProjection.word_span W σ n)
  rintro _ ⟨v, rfl⟩
  let cR := ((ScalarComparison.FreeRelativeScalarComparison.complexIso W R σ I δ).hom.f n).hom
  let cS := ((ScalarComparison.FreeRelativeScalarComparison.complexIso W S σ J ε).hom.f n).hom
  let g := ((PD.RelativeScalarMap.PDRelativeScalarMap.complexMap W R S GR GS φ hW f.toRingHom h IR γR IS γS hf).f n).hom
  change g (cR (a ⊗ₜ[W] exteriorPower.ιMulti W n (fun j => Finsupp.single (v j) 1))) =
    cS (f a ⊗ₜ[W] exteriorPower.ιMulti W n (fun j => Finsupp.single (v j) 1))
  have h₁ := congrArg g (ScalarComparison.FreeRelativeScalarComparison.word W R σ I δ n a v)
  have h₂ := PD.RelativeScalarMap.PDRelativeScalarMap.symbol W R S GR GS φ hW f.toRingHom h IR γR IS γS hf
    n a (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v)
  have hv : f.toRingHom ∘ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v) =
      (fun j => algebraMap S GS (b (v j)) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 (v j)) := funext (fun j => hX (v j))
  have h₃ := (congrArg (PD.DeRham.PDDeRham.symbol S GS IS γS (f a)) hv).trans
    (PD.FormTranslations.PDFormTranslations.add_base S GS IS γS (f a) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 ∘ v) (b ∘ v))
  exact h₁.trans (h₂.trans (h₃.trans (ScalarComparison.FreeRelativeScalarComparison.word W S σ J ε n (f a) v).symm))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.ScalarNaturality.FreeRelativeScalarNaturality
