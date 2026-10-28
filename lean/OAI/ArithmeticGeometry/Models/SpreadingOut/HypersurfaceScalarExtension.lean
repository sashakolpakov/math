import OAI.ArithmeticGeometry.Models.SpreadingOut.AbsoluteIrreducibility
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Ideal.Maximal

/-! # Hypersurface Scalar Extension -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceScalarExtension.Construction

noncomputable section

/-! Hypersurface scalar extension and the domain criterion for absolute
polynomial irreducibility. -/

open scoped TensorProduct

universe u

def hypersurfaceScalarExtensionIso
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {σ : Type*} (p : MvPolynomial σ R) :
    K ⊗[R] (MvPolynomial σ R ⧸ Ideal.span ({p} : Set (MvPolynomial σ R))) ≃ₐ[K]
      MvPolynomial σ K ⧸ Ideal.span ({MvPolynomial.map (algebraMap R K) p} : Set _) := by
  let I := Ideal.span ({p} : Set (MvPolynomial σ R))
  let e : K ⊗[R] MvPolynomial σ R ≃ₐ[K] MvPolynomial σ K :=
    MvPolynomial.algebraTensorAlgEquiv R K
  refine (Algebra.TensorProduct.tensorQuotientEquiv K (MvPolynomial σ R) K I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.span {MvPolynomial.map (algebraMap R K) p} =
    Ideal.map e.toRingHom (Ideal.map
      (Algebra.TensorProduct.includeRight : MvPolynomial σ R →ₐ[R] K ⊗[R] MvPolynomial σ R).toRingHom
      (Ideal.span {p}))
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  congr 1
  apply congrArg Set.singleton
  exact ((MvPolynomial.algebraTensorAlgEquiv_tmul R K 1 p).trans (one_smul _ _)).symm

theorem polynomial_irreducible_of_tensor_quotient_domain
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {σ : Type*} (p : MvPolynomial σ k) (hp : p ≠ 0)
    [IsDomain (K ⊗[k] (MvPolynomial σ k ⧸ Ideal.span ({p} : Set _)))] :
    Irreducible (MvPolynomial.map (algebraMap k K) p) := by
  let e := hypersurfaceScalarExtensionIso k K p
  have : IsDomain (MvPolynomial σ K ⧸ Ideal.span ({MvPolynomial.map (algebraMap k K) p} : Set _)) :=
    Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  have hprime := (Ideal.Quotient.isDomain_iff_prime
    (Ideal.span ({MvPolynomial.map (algebraMap k K) p} : Set _))).mp this
  have hp' : MvPolynomial.map (algebraMap k K) p ≠ 0 := by
    exact fun h ↦ hp (MvPolynomial.map_injective (algebraMap k K) (algebraMap k K).injective
      (h.trans (map_zero _).symm))
  exact ((Ideal.span_singleton_prime hp').mp hprime).irreducible

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceScalarExtension.Construction
