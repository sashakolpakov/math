import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.TensorIsomorphismNeighborhood
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Algebra Isomorphism Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.AlgebraIsomorphismNeighborhood

noncomputable section

/-! A finite algebra over a noetherian ring that becomes the base ring
at a local spectrum already does so on a principal open neighborhood. -/

open TensorProduct

universe u v w
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

theorem tensor_algebraMap_bijective_iff
    (B : Type w) [CommRing B] [Algebra R B] :
    Function.Bijective ((Algebra.linearMap R A).lTensor B) ↔
      Function.Bijective (algebraMap B (B ⊗[R] A)) := by
  let e := TensorProduct.rid R B
  have he : (fun b : B => (Algebra.linearMap R A).lTensor B (e.symm b)) =
      algebraMap B (B ⊗[R] A) := by
    funext b
    simp only [e, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
      map_one, Algebra.TensorProduct.algebraMap_apply]
    rfl
  constructor
  · intro h
    rw [← he]
    exact h.comp e.symm.bijective
  · intro h
    have hf : (fun x : B ⊗[R] R => (Algebra.linearMap R A).lTensor B x) =
        fun x => algebraMap B (B ⊗[R] A) (e x) := by
      funext x
      rw [← he]
      exact congrArg ((Algebra.linearMap R A).lTensor B) (e.symm_apply_apply x).symm
    rw [show ((Algebra.linearMap R A).lTensor B : B ⊗[R] R → B ⊗[R] A) =
      (fun x => algebraMap B (B ⊗[R] A) (e x)) from hf]
    exact h.comp e.bijective

theorem exists_principalOpen_algebra_isomorphism [IsNoetherianRing R] [Module.Finite R A]
    (p : PrimeSpectrum R)
    (hp : Function.Bijective (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] A))) :
    ∃ r ∉ p.asIdeal, Function.Bijective (algebraMap (Localization.Away r)
      (Localization.Away r ⊗[R] A)) := by
  obtain ⟨r, hr, h⟩ := TensorIsomorphismNeighborhood.exists_principalOpen_tensor_isomorphism (Algebra.linearMap R A) p
    ((tensor_algebraMap_bijective_iff (R := R) (A := A) (Localization.AtPrime p.asIdeal)).mpr hp)
  exact ⟨r, hr, (tensor_algebraMap_bijective_iff (R := R) (A := A) (Localization.Away r)).mp h⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.AlgebraIsomorphismNeighborhood
