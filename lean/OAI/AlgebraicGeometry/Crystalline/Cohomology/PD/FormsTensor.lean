import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrderedPD
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Forms Tensor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor.PDFormsTensor

noncomputable section

/-!
# Coordinate tensor descriptions of actual PD forms

When coordinate differentials form a basis, the tensor of the coefficient
algebra with the exterior powers of the free coordinate module is
canonically isomorphic to the actual PD form module. The map sends a
coordinate wedge to the corresponding differential symbol.
-/

open scoped TensorProduct

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I) (x : σ → A)

def coordinateLinear : (σ →₀ R) →ₗ[R] A := Finsupp.linearCombination R x

theorem coordinateLinear_single (i : σ) : coordinateLinear R A σ x (Finsupp.single i 1) = x i :=
  (Finsupp.linearCombination_single R 1 i).trans (one_smul R _)

def exteriorMap (n : ℕ) : (⋀[R]^n (σ →₀ R)) →ₗ[R] DeRham.PDDeRham.Form R A I δ n :=
  exteriorPower.alternatingMapLinearEquiv
    ((OrderedPD.OrderedPDSymbols.symbols R A I δ n).compLinearMap (coordinateLinear R A σ x))

def toForms (n : ℕ) : Koszul.Tensor.KoszulTensor.Term R σ A n →ₗ[A] DeRham.PDDeRham.Form R A I δ n :=
  (exteriorMap R A σ I δ x n).liftBaseChange A

theorem toForms_word (n : ℕ) (a : A) (v : Fin n → σ) :
    toForms R A σ I δ x n (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) 1)) =
      DeRham.PDDeRham.symbol R A I δ a (x ∘ v) := by
  rw [toForms, LinearMap.liftBaseChange_tmul, exteriorMap,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply, OrderedPD.OrderedPDSymbols.symbols_apply]
  have hv : (fun k => coordinateLinear R A σ x (Finsupp.single (v k) 1)) = x ∘ v :=
    funext (fun k => coordinateLinear_single R A σ x (v k))
  rw [hv, DeRham.PDDeRham.symbol_smul_one R A I δ a]

variable [LinearOrder σ]
  (b : Module.Basis σ A (DeRham.PDDeRham.Form R A I δ 1))
  (hb : ∀ i, b i = OneForms.PDOneForms.D R A I δ (x i))

def tensorBasis (n : ℕ) : Module.Basis (Set.powersetCard σ n) A (Koszul.Tensor.KoszulTensor.Term R σ A n) :=
  ((Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower n).baseChange A

def basisEquiv (n : ℕ) : Koszul.Tensor.KoszulTensor.Term R σ A n ≃ₗ[A] DeRham.PDDeRham.Form R A I δ n :=
  (tensorBasis R A σ n).equiv (OrderedPD.OrderedPDSymbols.basis R A I δ x b hb n) (Equiv.refl _)

theorem toForms_tensorBasis (n : ℕ) (s : Set.powersetCard σ n) :
    toForms R A σ I δ x n (tensorBasis R A σ n s) = OrderedPD.OrderedPDSymbols.basis R A I δ x b hb n s := by
  rw [tensorBasis, Module.Basis.baseChange_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, OrderedPD.OrderedPDSymbols.basis_apply]
  exact toForms_word R A σ I δ x n 1 (Set.powersetCard.ofFinEmbEquiv.symm s)

theorem toForms_eq_basisEquiv (n : ℕ) :
    toForms R A σ I δ x n = (basisEquiv R A σ I δ x b hb n).toLinearMap := by
  apply (tensorBasis R A σ n).ext
  intro s
  rw [toForms_tensorBasis]
  exact ((tensorBasis R A σ n).equiv_apply s
    (OrderedPD.OrderedPDSymbols.basis R A I δ x b hb n) (Equiv.refl _)).symm

/-- An isomorphism of actual PD form modules, with its coordinate symbol formula. -/
def formsEquiv (n : ℕ) : Koszul.Tensor.KoszulTensor.Term R σ A n ≃ₗ[A] DeRham.PDDeRham.Form R A I δ n :=
  LinearEquiv.ofBijective (toForms R A σ I δ x n) (by
    rw [toForms_eq_basisEquiv R A σ I δ x b hb n]
    exact (basisEquiv R A σ I δ x b hb n).bijective)

theorem formsEquiv_word (n : ℕ) (a : A) (v : Fin n → σ) :
    formsEquiv R A σ I δ x b hb n
      (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) 1)) =
        DeRham.PDDeRham.symbol R A I δ a (x ∘ v) := toForms_word R A σ I δ x n a v

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor.PDFormsTensor
