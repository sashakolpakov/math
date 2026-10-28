import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare

/-! # Coordinate Symbols -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.CoordinateSymbols.FreeRelativeCoordinateSymbols

noncomputable section

/-! # Coordinate symbols under the original free relative PD comparison -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I) [Fintype σ]

local notation "P" => MvPolynomial σ R
local notation "IP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.polynomialIdeal R σ I
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ IP
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ IP
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ IP
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.algebraEquiv R σ I δ
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP

attribute [local instance] Envelope.FreeRelativeEnvelope.envelopeBaseAlgebra

omit [Fintype σ] in
theorem coordinate (i : σ) : e (c i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  Envelope.FreeRelativeEnvelope.toDivided_coordinate R σ I δ i

theorem word (n : ℕ) (a : G) (v : Fin n → σ) :
    ((Poincare.FreeRelativePoincare.complexIso R σ I δ).hom.f n).hom
      (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun j => Finsupp.single (v j) 1)) =
        PD.DeRham.PDDeRham.symbol R G IG γ a (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v) := by
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let w : ⋀[R]^n (σ →₀ R) := exteriorPower.ιMulti R n (fun j => Finsupp.single (v j) 1)
  let f₁ : G ⊗[R] (⋀[R]^n (σ →₀ R)) →ₗ[R] E ⊗[R] (⋀[R]^n (σ →₀ R)) :=
    ((Poincare.FreeRelativePoincare.tensorIso R σ I δ).inv.f n).hom
  let f₂ : E ⊗[R] (⋀[R]^n (σ →₀ R)) →ₗ[R] PD.DeRham.PDDeRham.Form R E IE ε n :=
    ((Poincare.FreeRelativePoincare.envelopeFormsIso R σ I δ).hom.f n).hom
  let f₃ : PD.DeRham.PDDeRham.Form R E IE ε n →ₗ[R] PD.DeRham.PDDeRham.Form R G IG γ n :=
    ((Poincare.FreeRelativePoincare.dividedFormsIso R σ I δ).hom.f n).hom
  have h₁ : f₁ (a ⊗ₜ[R] w) = (e).symm a ⊗ₜ[R] w := rfl
  have h₂ : f₂ ((e).symm a ⊗ₜ[R] w) = PD.DeRham.PDDeRham.symbol R E IE ε ((e).symm a) (c ∘ v) :=
    PD.FormsTensor.PDFormsTensor.formsEquiv_word R E σ IE ε c
      (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.basis R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I))
      (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.basis_apply R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I)) n ((e).symm a) v
  have h₃ : f₃ (PD.DeRham.PDDeRham.symbol R E IE ε ((e).symm a) (c ∘ v)) =
      PD.DeRham.PDDeRham.symbol R G IG γ a (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v) := by
    have h := PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (A := CommAlgCat.of R E) (B := CommAlgCat.of R G)
      (CommAlgCat.ofHom (e).toAlgHom) (Envelope.FreeRelativeEnvelope.algebraEquiv_isDPMorphism R σ I δ)
      n ((e).symm a) (c ∘ v)
    change f₃ _ = PD.DeRham.PDDeRham.symbol R G IG γ (e ((e).symm a)) (e ∘ (c ∘ v)) at h
    rw [AlgEquiv.apply_symm_apply] at h
    have hv : e ∘ (c ∘ v) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v := funext (fun j => coordinate R σ I δ (v j))
    exact h.trans (congrArg (PD.DeRham.PDDeRham.symbol R G IG γ a) hv)
  change f₃ (f₂ (f₁ (a ⊗ₜ[R] w))) = _
  exact (congrArg (fun y => f₃ (f₂ y)) h₁).trans ((congrArg f₃ h₂).trans h₃)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.CoordinateSymbols.FreeRelativeCoordinateSymbols
