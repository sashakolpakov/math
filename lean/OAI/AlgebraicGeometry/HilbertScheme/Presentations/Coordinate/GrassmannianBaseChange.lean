import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SubmoduleExtension
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Grassmannian Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian

noncomputable section

/-!
Base change of actual coordinate Grassmannian quotients. Their relations
extend as submodules, and the new quotient is the tensor product of the
original finite projective quotient.
-/

open TensorProduct

universe u

variable {R S ν : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Fintype ν] [DecidableEq ν]

theorem coordinateSubmoduleExtension_eq_baseChange (N : Submodule R (ν → R)) :
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R S) N =
      (N.baseChange S).map (TensorProduct.piScalarRight R S S ν).toLinearMap := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, ← Set.image_comp]
  have hc : (fun x : ν → R => algebraMap R S ∘ x) =
      (TensorProduct.piScalarRight R S S ν).toLinearMap ∘ TensorProduct.mk R S (ν → R) 1 := by
    funext x j
    simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Function.comp_apply, Algebra.smul_def]
  exact congrArg (Submodule.span S) (congrArg (fun f => f '' (N : Set (ν → R))) hc)

omit [Fintype ν] [DecidableEq ν] in
theorem quotientMk_baseChange_kernel (N : Submodule R (ν → R)) :
    (N.mkQ.baseChange S).ker = N.baseChange S := by
  apply Submodule.restrictScalars_injective R
  exact lTensor_mkQ S N

def coordinateBaseChangeQuotientMap (N : Submodule R (ν → R)) :
    (ν → S) →ₗ[S] S ⊗[R] ((ν → R) ⧸ N) :=
  (N.mkQ.baseChange S).comp (TensorProduct.piScalarRight R S S ν).symm.toLinearMap

theorem coordinateBaseChangeQuotientMap_surjective (N : Submodule R (ν → R)) :
    Function.Surjective (coordinateBaseChangeQuotientMap (S := S) N) :=
  (LinearMap.baseChange_surjective S N.mkQ_surjective).comp
    (TensorProduct.piScalarRight R S S ν).symm.surjective

theorem coordinateBaseChangeQuotientMap_kernel (N : Submodule R (ν → R)) :
    (coordinateBaseChangeQuotientMap (S := S) N).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R S) N := by
  rw [coordinateBaseChangeQuotientMap, LinearMap.ker_comp, quotientMk_baseChange_kernel,
    Submodule.comap_equiv_eq_map_symm, coordinateSubmoduleExtension_eq_baseChange]
  rfl

def coordinateBaseChangeQuotientEquiv (N : Submodule R (ν → R)) :
    ((ν → S) ⧸ Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R S) N) ≃ₗ[S] S ⊗[R] ((ν → R) ⧸ N) :=
  (Submodule.quotEquivOfEq _ _ (coordinateBaseChangeQuotientMap_kernel (S := S) N).symm) ≪≫ₗ
    (coordinateBaseChangeQuotientMap (S := S) N).quotKerEquivOfSurjective
      (coordinateBaseChangeQuotientMap_surjective N)

def coordinateGrassmannianBaseChange {k : ℕ} (N : Module.Grassmannian R (ν → R) k) :
    Module.Grassmannian S (ν → S) k where
  toSubmodule := Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R S) N.toSubmodule
  finite_quotient := Module.Finite.equiv (coordinateBaseChangeQuotientEquiv (S := S) N.toSubmodule).symm
  projective_quotient := Module.Projective.of_equiv (coordinateBaseChangeQuotientEquiv (S := S) N.toSubmodule).symm
  rankAtStalk_eq p := by
    rw [congrFun (Module.rankAtStalk_eq_of_equiv
      (coordinateBaseChangeQuotientEquiv (S := S) N.toSubmodule)) p,
      Module.rankAtStalk_baseChange]
    exact N.rankAtStalk_eq _

omit [Algebra R S] in
def coordinateGrassmannianMap {k : ℕ} (φ : R →+* S) (N : Module.Grassmannian R (ν → R) k) :
    Module.Grassmannian S (ν → S) k :=
  letI := φ.toAlgebra
  coordinateGrassmannianBaseChange N

omit [Algebra R S] in
theorem coordinateGrassmannianMap_toSubmodule {k : ℕ} (φ : R →+* S)
    (N : Module.Grassmannian R (ν → R) k) :
    (coordinateGrassmannianMap φ N).toSubmodule = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ N.toSubmodule := rfl

theorem coordinateGrassmannianMap_id {k : ℕ} (N : Module.Grassmannian R (ν → R) k) :
    coordinateGrassmannianMap (RingHom.id R) N = N := by
  apply Module.Grassmannian.ext
  exact SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_id N.toSubmodule

omit [Algebra R S] in
theorem coordinateGrassmannianMap_comp {A : Type u} [CommRing A] {k : ℕ}
    (φ : R →+* S) (ψ : S →+* A) (N : Module.Grassmannian R (ν → R) k) :
    coordinateGrassmannianMap (ψ.comp φ) N = coordinateGrassmannianMap ψ (coordinateGrassmannianMap φ N) := by
  apply Module.Grassmannian.ext
  exact SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp φ ψ N.toSubmodule

omit [Algebra R S] in
theorem coordinateGrassmannianMap_normalized {ι : Type u} [Fintype ι] [DecidableEq ι]
    (φ : R →+* S) (a : ι → ν) (Q : Matrix ι ν R) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    coordinateGrassmannianMap φ (Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) =
      Normalized.Quotients.Grassmannian.normalizedGrassmannian a (Q.map φ) (hQ.map φ) := by
  apply Module.Grassmannian.ext
  exact Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ a Q hQ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian
