import OAI.ArithmeticGeometry.Models.SpreadingOut.CommonOpenAlgebra
import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceScalarExtension
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Hypersurface Chart -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceChart.Construction

noncomputable section

/-! Multivariate hypersurface charts obtained from integral primitive generators. -/

open scoped TensorProduct

universe u

def monogenicHypersurfaceIso
    (k A : Type u) [Field k] [CommRing A] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) k) A] (a : A) :
    (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span
      ({(MvPolynomial.finSuccEquiv k n).symm (minpoly (MvPolynomial (Fin n) k) a)} : Set _)) ≃ₐ[k]
      AdjoinRoot (minpoly (MvPolynomial (Fin n) k) a) := by
  apply Ideal.quotientEquivAlg _ _ (MvPolynomial.finSuccEquiv k n)
  rw [Ideal.map_span, Set.image_singleton]
  congr 1
  apply congrArg Set.singleton
  exact ((MvPolynomial.finSuccEquiv k n).apply_symm_apply _).symm

theorem tensor_domain_of_injective_algebra_map
    (k K A B : Type u) [Field k] [CommRing K] [CommRing A] [CommRing B]
    [Algebra k K] [Algebra k A] [Algebra k B]
    [IsDomain (K ⊗[k] B)] (f : A →ₐ[k] B) (hf : Function.Injective f) :
    IsDomain (K ⊗[k] A) := by
  let g : K ⊗[k] A →ₐ[k] K ⊗[k] B := Algebra.TensorProduct.map (AlgHom.id k K) f
  have hg : Function.Injective g := by
    change Function.Injective (f.toLinearMap.lTensor K)
    exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  exact Function.Injective.isDomain g.toRingHom hg

theorem monogenic_hypersurface_absolute_irreducible
    (k K A : Type u) [Field k] [Field K] [CommRing A] [IsDomain A]
    [Algebra k K] [Algebra k A] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) k) A] [IsScalarTower k (MvPolynomial (Fin n) k) A]
    [FaithfulSMul (MvPolynomial (Fin n) k) A]
    [IsDomain (K ⊗[k] A)] (a : A) (ha : IsIntegral (MvPolynomial (Fin n) k) a) :
    Irreducible (MvPolynomial.map (algebraMap k K)
      ((MvPolynomial.finSuccEquiv k n).symm (minpoly (MvPolynomial (Fin n) k) a))) := by
  let P := MvPolynomial (Fin n) k
  let p := (MvPolynomial.finSuccEquiv k n).symm (minpoly P a)
  let C := MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span ({p} : Set _)
  let e := monogenicHypersurfaceIso k A n a
  let j : AdjoinRoot (minpoly P a) →ₐ[P] A :=
    (Algebra.adjoin P ({a} : Set A)).val.comp (minpoly.equivAdjoin ha).toAlgHom
  let f : C →ₐ[k] A := (j.restrictScalars k).comp e.toAlgHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp ((minpoly.equivAdjoin ha).injective.comp e.injective)
  have : IsDomain (K ⊗[k] C) := tensor_domain_of_injective_algebra_map k K C A f hf
  apply HypersurfaceScalarExtension.Construction.polynomial_irreducible_of_tensor_quotient_domain k K p
  intro h
  apply minpoly.ne_zero ha
  have H := congrArg (MvPolynomial.finSuccEquiv k n) h
  simpa only [p, AlgEquiv.apply_symm_apply, map_zero] using H

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceChart.Construction
