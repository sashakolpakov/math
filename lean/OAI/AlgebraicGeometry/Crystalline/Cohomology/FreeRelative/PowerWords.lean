import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormPowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormTranslations
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.RelativeScalarSquare

/-! # Power Words -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerWords.FreeRelativePowerWords

noncomputable section

/-! # The actual power-coordinate map on every coordinate exterior word -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (W R σ : Type u) [CommRing W] [CommRing R] [Algebra W R]
  (I : Ideal R) (δ : DividedPowers I) [Fintype σ] [LinearOrder σ]
  (m : ℕ) (a c : σ → R) (h : ∀ i, a i ^ m - c i ∈ I)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
local notation "f" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerMap.FreeRelativePowerMap.map R σ I δ m a c h

def complexMap := PD.RelativeScalarSquare.PDRelativeScalarSquare.selfMap W R G IG γ f
  (PowerMap.FreeRelativePowerMap.map_isDPMorphism R σ I δ m a c h)

def jacobian (n : ℕ) (v : Fin n → σ) : G :=
  ∏ j, ((m : G) * PowerMap.FreeRelativePowerMap.total R σ a (v j) ^ (m - 1))

omit [Fintype σ] [LinearOrder σ] in
theorem symbol (n : ℕ) (b : G) (v : Fin n → σ) :
    ((complexMap W R σ I δ m a c h).f n).hom
      (PD.DeRham.PDDeRham.symbol R G IG γ b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v)) =
    PD.DeRham.PDDeRham.symbol R G IG γ (f b * jacobian R σ m a n v) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v) := by
  have hc := PD.FormTranslations.PDFormTranslations.add_base R G IG γ b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v) (c ∘ v)
  have ha := PD.FormTranslations.PDFormTranslations.add_base R G IG γ (f b * jacobian R σ m a n v)
    (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v) (a ∘ v)
  let g := ((complexMap W R σ I δ m a c h).f n).hom
  have hs := PD.RelativeScalarSquare.PDRelativeScalarSquare.selfMap_symbol W R G IG γ f
    (PowerMap.FreeRelativePowerMap.map_isDPMorphism R σ I δ m a c h) n b
    (PowerMap.FreeRelativePowerMap.total R σ c ∘ v)
  have hv : f ∘ (PowerMap.FreeRelativePowerMap.total R σ c ∘ v) =
      (fun j => PowerMap.FreeRelativePowerMap.total R σ a (v j) ^ m) :=
    funext (fun j => PowerMap.FreeRelativePowerMap.map_total R σ I δ m a c h (v j))
  have hp := PD.FormPowers.PDFormPowers.pow R G IG γ (f b) (PowerMap.FreeRelativePowerMap.total R σ a ∘ v) m
  exact (congrArg g hc.symm).trans
    (hs.trans ((congrArg (PD.DeRham.PDDeRham.symbol R G IG γ (f b)) hv).trans (hp.trans ha)))

theorem word (n : ℕ) (b : G) (v : Fin n → σ) :
    ((complexMap W R σ I δ m a c h).f n).hom
      (((ScalarComparison.FreeRelativeScalarComparison.complexIso W R σ I δ).hom.f n).hom
        (b ⊗ₜ[W] exteriorPower.ιMulti W n (fun j => Finsupp.single (v j) 1))) =
    ((ScalarComparison.FreeRelativeScalarComparison.complexIso W R σ I δ).hom.f n).hom
      ((f b * jacobian R σ m a n v) ⊗ₜ[W]
        exteriorPower.ιMulti W n (fun j => Finsupp.single (v j) 1)) := by
  rw [ScalarComparison.FreeRelativeScalarComparison.word, ScalarComparison.FreeRelativeScalarComparison.word]
  exact symbol W R σ I δ m a c h n b v

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerWords.FreeRelativePowerWords
