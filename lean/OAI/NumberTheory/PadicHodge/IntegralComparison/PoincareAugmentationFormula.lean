import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare

/-! # Poincare Augmentation Formula -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PoincareAugmentationFormula

noncomputable section

/-!
# IntegralComparison: the integral Poincaré augmentation is the canonical inclusion of constants

The proved contraction uses several coordinate identifications. Their
formula on tensor words identifies its augmentation with the canonical
degree-zero differential symbol, which is natural under restriction.
-/

open _root_.CategoryTheory
open scoped TensorProduct

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

attribute [local instance] AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.envelopeBaseAlgebra

theorem tensorIso_inv_tmul (n : ℕ) (a : G) (ω : ⋀[R]^n (σ →₀ R)) :
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.tensorIso R σ I δ).inv.f n (a ⊗ₜ[R] ω) = (e).symm a ⊗ₜ[R] ω := by
  change TensorProduct.congr (e).toLinearEquiv.symm (LinearEquiv.refl R _).symm (a ⊗ₜ[R] ω) = _
  rw [TensorProduct.congr_tmul]
  rfl

theorem envelopeFormsIso_hom_word [LinearOrder σ] (n : ℕ) (a : E) (v : Fin n → σ) :
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.envelopeFormsIso R σ I δ).hom.f n
      (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1)) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R E IE ε a (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.coordinate R σ I δ ∘ v) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor.PDFormsTensor.formsEquiv_word R E σ IE ε (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.coordinate R σ I δ)
    (AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.basis R σ I δ IP (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.base_le R σ I))
    (AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.basis_apply R σ I δ IP (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.base_le R σ I)) n a v

omit [Fintype σ] in
theorem dividedFormsIso_hom_symbol (n : ℕ) (a : E) (v : Fin n → E) :
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.dividedFormsIso R σ I δ).hom.f n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R E IE ε a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R G IG γ (e a) (fun i => e (v i)) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (CommAlgCat.ofHom (e).toAlgHom)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.algebraEquiv_isDPMorphism R σ I δ) n a v

omit [Fintype σ] in
theorem coordinate_image (i : σ) : e (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.coordinate R σ I δ i) =
    AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.toDivided_coordinate R σ I δ i

theorem complexIso_hom_word (n : ℕ) (a : G) (v : Fin n → σ) :
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.complexIso R σ I δ).hom.f n
      (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1)) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R G IG γ a (fun i => AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 (v i)) := by
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  change (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.dividedFormsIso R σ I δ).hom.f n
    ((AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.envelopeFormsIso R σ I δ).hom.f n
      ((AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.tensorIso R σ I δ).inv.f n
        (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1)))) = _
  rw [tensorIso_inv_tmul, envelopeFormsIso_hom_word, dividedFormsIso_hom_symbol,
    AlgEquiv.apply_symm_apply]
  simp only [Function.comp_apply, coordinate_image]
  rfl

theorem koszul_hom_zero : (AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.homotopyEquiv R σ).hom.f 0 =
    AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.inclusionHom R σ :=
  AlgebraicGeometry.Crystalline.Cohomology.SingleRetraction.SingleRetractionHomotopy.augmentation_zero (AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.complex R σ)
    (ModuleCat.of R R) (AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.inclusionHom R σ)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.differential_inclusionHom R σ)

omit [Fintype σ] in
theorem exterior_zero_word : (exteriorPower.zeroEquiv R (σ →₀ R)).symm 1 =
    exteriorPower.ιMulti R 0 (fun i : Fin 0 => Finsupp.single (Fin.elim0 i : σ) 1) := by
  apply (exteriorPower.zeroEquiv R (σ →₀ R)).injective
  rw [LinearEquiv.apply_symm_apply, exteriorPower.zeroEquiv_ιMulti]

/-- The proved Poincaré quasi-isomorphism is the canonical inclusion of constants. -/
theorem augmentation_zero (r : R) :
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.augmentation R σ I δ).f 0 r =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R G IG γ (algebraMap R G r) (fun i : Fin 0 => Fin.elim0 i) := by
  change (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.complexIso R σ I δ).hom.f 0
    ((AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.homotopyEquiv R σ).hom.f 0 r) = _
  rw [koszul_hom_zero]
  change (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.complexIso R σ I δ).hom.f 0
    (AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.inclusionZero R σ r) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.inclusionZero_apply, exterior_zero_word, complexIso_hom_word]
  congr 1
  funext i
  exact Fin.elim0 i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PoincareAugmentationFormula
