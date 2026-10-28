import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Tensor.BundleCycles

noncomputable section

section

/-! Base change of the actual extended Rees algebra maps into the
Laurent algebra. Flat coefficients preserve this genuine embedding. -/

open scoped TensorProduct

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S] [Algebra R S]

def deformationTensorToLaurent : S ⊗[R] Iff.BundleCycles.deformationAlgebra I →ₐ[S] LaurentPolynomial S :=
  (AddMonoidAlgebra.scalarTensorEquiv R S (M := ℤ)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id S S) (Iff.BundleCycles.deformationAlgebra I).val)

theorem deformationTensorToLaurent_tmul (s : S) (a : Iff.BundleCycles.deformationAlgebra I) :
    deformationTensorToLaurent I S (s ⊗ₜ[R] a) =
      s • AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) a.val := by
  rw [deformationTensorToLaurent, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]
  exact AddMonoidAlgebra.scalarTensorEquiv_tmul s a.val

theorem deformationTensorToLaurent_injective [Module.Flat R S] :
    Function.Injective (deformationTensorToLaurent I S) := by
  have h : Function.Injective ((Iff.BundleCycles.deformationAlgebra I).val.toLinearMap.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap (Iff.BundleCycles.deformationAlgebra I).val.toLinearMap Subtype.val_injective
  exact (AddMonoidAlgebra.scalarTensorEquiv R S (M := ℤ)).injective.comp h

end

section

/-! The image after any coefficient base change is exactly the extended
Rees algebra of the extended ideal. Every coefficient is retained. -/

open scoped TensorProduct BigOperators

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S] [Algebra R S]

theorem deformationTensorToLaurent_mem (a : S ⊗[R] Iff.BundleCycles.deformationAlgebra I) :
    deformationTensorToLaurent I S a ∈ Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)) := by
  induction a using TensorProduct.inductionOn with
  | tmul s b =>
    rw [deformationTensorToLaurent_tmul]
    exact (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S))).smul_mem
      (Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map b).property s
  | add a b ha hb =>
    rw [map_add]
    exact (Iff.BundleCycles.deformationAlgebra _).add_mem ha hb

theorem deformationTensorToLaurent_monomial_mem_range (n : ℤ) (s : S)
    (hs : s ∈ I.map (algebraMap R S) ^ (-n).toNat) :
    AddMonoidAlgebra.single n s ∈ (deformationTensorToLaurent I S).range := by
  let K : Ideal S := (deformationTensorToLaurent I S).range.toSubmodule.comap
    (AddMonoidAlgebra.lsingle (R := S) n)
  have hK : (I ^ (-n).toNat).map (algebraMap R S) ≤ K := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change AddMonoidAlgebra.single n (algebraMap R S r) ∈ (deformationTensorToLaurent I S).range
    refine ⟨1 ⊗ₜ[R] Iff.BundleCycles.deformationMonomial I n r hr, ?_⟩
    change deformationTensorToLaurent I S (1 ⊗ₜ[R] Iff.BundleCycles.deformationMonomial I n r hr) = _
    rw [deformationTensorToLaurent_tmul, one_smul]
    exact AddMonoidAlgebra.mapRingHom_single (algebraMap R S) n r
  have hs' : s ∈ (I ^ (-n).toNat).map (algebraMap R S) := by
    rwa [Ideal.map_pow]
  exact hK hs'

theorem deformationTensorToLaurent_range :
    (deformationTensorToLaurent I S).range = Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)) := by
  classical
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    exact deformationTensorToLaurent_mem I S b
  · intro a ha
    rw [← AddMonoidAlgebra.sum_coeff_single a]
    exact Subalgebra.sum_mem _ (fun n _ => deformationTensorToLaurent_monomial_mem_range I S n _ (ha n))

end

/-! Flat base change commutes with the actual deformation algebra,
by its proved Laurent embedding and complete coefficient image. -/

open scoped TensorProduct

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S] [Algebra R S]

def deformationBaseChange : S ⊗[R] Iff.BundleCycles.deformationAlgebra I →ₐ[S] Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)) :=
  (deformationTensorToLaurent I S).codRestrict (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)))
    (deformationTensorToLaurent_mem I S)

theorem deformationBaseChange_surjective : Function.Surjective (deformationBaseChange I S) := by
  intro a
  have ha : a.val ∈ (deformationTensorToLaurent I S).range :=
    (deformationTensorToLaurent_range I S).symm ▸ a.property
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, Subtype.ext hb⟩

theorem deformationBaseChange_injective [Module.Flat R S] : Function.Injective (deformationBaseChange I S) := by
  intro a b h
  exact deformationTensorToLaurent_injective I S (congrArg Subtype.val h)

def deformationBaseChangeEquiv [Module.Flat R S] :
    S ⊗[R] Iff.BundleCycles.deformationAlgebra I ≃ₐ[S] Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)) :=
  AlgEquiv.ofBijective (deformationBaseChange I S)
    ⟨deformationBaseChange_injective I S, deformationBaseChange_surjective I S⟩

theorem deformationBaseChange_tmul (s : S) (a : Iff.BundleCycles.deformationAlgebra I) :
    deformationBaseChange I S (s ⊗ₜ[R] a) =
      s • Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map a := by
  apply Subtype.ext
  exact deformationTensorToLaurent_tmul I S s a

theorem deformationBaseChange_parameter :
    deformationBaseChange I S (1 ⊗ₜ[R] Iff.BundleCycles.deformationParameter I) =
      Iff.BundleCycles.deformationParameter (I.map (algebraMap R S)) := by
  rw [deformationBaseChange_tmul, one_smul, Maps.BundleCycles.deformationMap_parameter]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Tensor.BundleCycles
