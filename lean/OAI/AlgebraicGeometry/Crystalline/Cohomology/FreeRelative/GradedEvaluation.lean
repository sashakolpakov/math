import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerWords
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor

/-! # Graded Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.GradedEvaluation.FreeRelativeGradedEvaluation

noncomputable section

/-! # Graded evaluation of relative free PD forms at specified coordinates

The maps here evaluate coefficients and send coordinate exterior words to
the specified coordinate differentials over the smaller base ring.
-/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

private theorem component_inverse (S : Type u) [CommRing S]
    {K L : CochainComplex (ModuleCat.{u} S) ℕ} (c : K ≅ L) (n : ℕ) (x : K.X n) :
    (c.inv.f n).hom ((c.hom.f n).hom x) = x := by
  have h : c.hom.f n ≫ c.inv.f n = 𝟙 (K.X n) := congrArg (fun f => f.f n) c.hom_inv_id
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x

variable (W R σ : Type u) [CommRing W] [CommRing R] [Algebra W R]
  (I : Ideal R) (δ : DividedPowers I) [Fintype σ] [LinearOrder σ]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ

variable (e : DividedPowerAlgebra R (σ →₀ R) →ₐ[R] R) (y : σ → R)

def tensorMap (n : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ G n →ₗ[W] PD.DeRham.PDDeRham.Form W R I δ n :=
  ((PD.FormsTensor.PDFormsTensor.toForms W R σ I δ y n).restrictScalars W).comp
    (TensorProduct.map (e.restrictScalars W).toLinearMap LinearMap.id)

def formMap (n : ℕ) : PD.DeRham.PDDeRham.Form R G IG γ n →+ PD.DeRham.PDDeRham.Form W R I δ n :=
  (tensorMap W R σ I δ e y n).toAddMonoidHom.comp
    ((ScalarComparison.FreeRelativeScalarComparison.complexIso W R σ I δ).inv.f n).hom.toAddMonoidHom

theorem comparison (n : ℕ) (t : Koszul.Tensor.KoszulTensor.Term W σ G n) :
    formMap W R σ I δ e y n (((ScalarComparison.FreeRelativeScalarComparison.complexIso W R σ I δ).hom.f n).hom t) =
      tensorMap W R σ I δ e y n t := by
  have h := component_inverse W (ScalarComparison.FreeRelativeScalarComparison.complexIso W R σ I δ) n t
  exact congrArg (fun z : Koszul.Tensor.KoszulTensor.Term W σ G n => tensorMap W R σ I δ e y n z) h

theorem symbol (n : ℕ) (b : G) (v : Fin n → σ) :
    formMap W R σ I δ e y n (PD.DeRham.PDDeRham.symbol R G IG γ b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v)) =
      PD.DeRham.PDDeRham.symbol W R I δ (e b) (y ∘ v) := by
  have h := comparison W R σ I δ e y n
    (b ⊗ₜ[W] exteriorPower.ιMulti W n (fun j => Finsupp.single (v j) 1))
  rw [ScalarComparison.FreeRelativeScalarComparison.word] at h
  exact h.trans (PD.FormsTensor.PDFormsTensor.toForms_word W R σ I δ y n (e b) v)

variable (m : ℕ) (a c : σ → R) (h : ∀ i, a i ^ m - c i ∈ I)
  (he : ∀ i, e (PowerMap.FreeRelativePowerMap.total R σ a i) = y i)

include he in
omit [CommRing W] [Algebra W R] [Fintype σ] [LinearOrder σ] in
theorem jacobian (n : ℕ) (v : Fin n → σ) :
    e (PowerWords.FreeRelativePowerWords.jacobian R σ m a n v) =
      ∏ j, ((m : R) * y (v j) ^ (m - 1)) := by
  change e (∏ j, ((m : G) * PowerMap.FreeRelativePowerMap.total R σ a (v j) ^ (m - 1))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_mul, map_natCast, map_pow, he]

include he in
theorem power_symbol (n : ℕ) (b : G) (v : Fin n → σ) :
    formMap W R σ I δ e y n
      (((PowerWords.FreeRelativePowerWords.complexMap W R σ I δ m a c h).f n).hom
        (PD.DeRham.PDDeRham.symbol R G IG γ b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v))) =
      PD.DeRham.PDDeRham.symbol W R I δ (e (PowerMap.FreeRelativePowerMap.map R σ I δ m a c h b))
        (fun j => y (v j) ^ m) := by
  rw [PowerWords.FreeRelativePowerWords.symbol, symbol, map_mul, jacobian R σ e y m a he]
  exact (PD.FormPowers.PDFormPowers.pow W R I δ (e (PowerMap.FreeRelativePowerMap.map R σ I δ m a c h b))
    (y ∘ v) m).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.GradedEvaluation.FreeRelativeGradedEvaluation
