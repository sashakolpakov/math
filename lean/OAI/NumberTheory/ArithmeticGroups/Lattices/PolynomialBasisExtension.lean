import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixFlatExtension
import OAI.NumberTheory.ArithmeticGroups.Lattices.GeneralVanishingBaseChange
import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialStabilizer

/-! # Polynomial Basis Extension -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialBasisExtension.Construction

noncomputable section

section

/-! Scalar extension of polynomial subspaces, including bounded-degree
pieces of vanishing ideals. -/

open scoped Classical TensorProduct
open _root_.MvPolynomial Set

def polynomialSubspaceExtension {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (W : Submodule k (MvPolynomial σ k)) : Submodule K (MvPolynomial σ K) :=
  (W.baseChange K).map (MvPolynomial.algebraTensorAlgEquiv k K).toLinearMap

theorem polynomialSubspaceExtension_inf
    {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (P Q : Submodule k (MvPolynomial σ k)) :
    polynomialSubspaceExtension (K := K) (P ⊓ Q) =
      polynomialSubspaceExtension P ⊓ polynomialSubspaceExtension Q := by
  unfold polynomialSubspaceExtension
  rw [MatrixFlatExtension.Construction.submodule_baseChange_inf, Submodule.map_inf _ (MvPolynomial.algebraTensorAlgEquiv k K).injective]

theorem polynomialSubspaceExtension_restrictSupport
    {k K σ : Type*} [Field k] [Field K] [Algebra k K] (s : Set (σ →₀ ℕ)) :
    polynomialSubspaceExtension (K := K) (restrictSupport k s) = restrictSupport K s := by
  unfold polynomialSubspaceExtension
  rw [restrictSupport_eq_span, Submodule.baseChange_span, Submodule.map_span,
    image_image, image_image, restrictSupport_eq_span]
  congr 1
  congr 1
  funext m
  change MvPolynomial.algebraTensorAlgEquiv k K (1 ⊗ₜ[k] monomial m (1 : k)) = monomial m 1
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
  simp

theorem ideal_submodule_baseChange
    {k K A : Type*} [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    (I : Ideal A) :
    (I.restrictScalars k).baseChange K =
      (I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)).restrictScalars K := by
  apply Submodule.restrictScalars_injective k
  change LinearMap.range (LinearMap.lTensor K (I.restrictScalars k).subtype) = _
  exact (Ideal.map_includeRight_eq I).symm

theorem ideal_map_equiv_restrictScalars
    {k A B : Type*} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (e : A ≃ₐ[k] B) (I : Ideal A) :
    (I.restrictScalars k).map e.toLinearMap = (I.map e.toRingHom).restrictScalars k := by
  ext x
  change (∃ y, y ∈ I ∧ e y = x) ↔ x ∈ I.map e.toRingHom
  exact (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).symm

theorem polynomialSubspaceExtension_ideal
    {k K σ : Type*} [Field k] [Field K] [Algebra k K] (I : Ideal (MvPolynomial σ k)) :
    polynomialSubspaceExtension (K := K) (I.restrictScalars k) =
      (I.map (MvPolynomial.map (algebraMap k K))).restrictScalars K := by
  unfold polynomialSubspaceExtension
  rw [ideal_submodule_baseChange, ideal_map_equiv_restrictScalars]
  let e : K ⊗[k] MvPolynomial σ k ≃ₐ[K] MvPolynomial σ K := MvPolynomial.algebraTensorAlgEquiv k K
  let f : MvPolynomial σ k →ₐ[k] K ⊗[k] MvPolynomial σ k := Algebra.TensorProduct.includeRight
  have he : e.toRingHom.comp f.toRingHom = MvPolynomial.map (algebraMap k K) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.algebraTensorAlgEquiv k K (1 ⊗ₜ[k] p) = MvPolynomial.map (algebraMap k K) p
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  have hI : (I.map f.toRingHom).map e.toRingHom = I.map (MvPolynomial.map (algebraMap k K)) := by
    rw [Ideal.map_map, he]
  exact congrArg (fun J : Ideal (MvPolynomial σ K) => J.restrictScalars K) hI

theorem boundedVanishingSpace_baseChange
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (d : ℕ) :
    polynomialSubspaceExtension (K := K) (PolynomialStabilizer.Construction.boundedVanishingSpace G d) =
      PolynomialStabilizer.Construction.boundedVanishingSpace (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) d := by
  unfold PolynomialStabilizer.Construction.boundedVanishingSpace
  rw [polynomialSubspaceExtension_inf, polynomialSubspaceExtension_ideal,
    ← GeneralVanishingBaseChange.Construction.vanishingIdeal_charZero_baseChange G hG]
  congr 1
  exact polynomialSubspaceExtension_restrictSupport _

end

/-! Extending a polynomial-subspace basis coefficientwise gives a basis
of the extended subspace. -/

open scoped Classical TensorProduct
open Set

theorem polynomial_basis_extension
    {k K σ ι : Type*} [Field k] [Field K] [Algebra k K]
    (W : Submodule k (MvPolynomial σ k)) (b : Module.Basis ι k W) :
    LinearIndependent K (fun i => MvPolynomial.map (algebraMap k K) (b i).val) ∧
      Submodule.span K (range (fun i => MvPolynomial.map (algebraMap k K) (b i).val)) =
        polynomialSubspaceExtension (K := K) W := by
  let e : K ⊗[k] MvPolynomial σ k ≃ₐ[K] MvPolynomial σ K := MvPolynomial.algebraTensorAlgEquiv k K
  let T : K ⊗[k] W →ₗ[K] MvPolynomial σ K := e.toLinearMap.comp (W.subtype.baseChange K)
  have hinj : Function.Injective T := e.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype W.injective_subtype)
  have hb : T ∘ b.baseChange K = fun i => MvPolynomial.map (algebraMap k K) (b i).val := by
    funext i
    change e (W.subtype.baseChange K (b.baseChange K i)) = _
    rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
    exact (MvPolynomial.algebraTensorAlgEquiv_tmul k K 1 (b i).val).trans (one_smul K _)
  constructor
  · rw [← hb]
    exact (b.baseChange K).linearIndependent.map' T (LinearMap.ker_eq_bot.mpr hinj)
  · rw [← hb, range_comp, ← Submodule.map_span, (b.baseChange K).span_eq, Submodule.map_top]
    change LinearMap.range (e.toLinearMap.comp (W.subtype.baseChange K)) = _
    rw [LinearMap.range_comp]
    rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialBasisExtension.Construction
