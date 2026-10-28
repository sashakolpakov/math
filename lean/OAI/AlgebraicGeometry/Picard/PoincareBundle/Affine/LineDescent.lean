import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent

noncomputable section

/-!
# Faithfully flat descent of invertible modules for PoincareBundle

The contraction map M* tensor M → R detects invertibility. For a finitely
presented module, flat base change commutes with its dual, so faithful
flatness detects invertibility of the contraction map. This is the
affine algebra needed for descent of algebraic line bundles.
-/

open TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Flat base change commutes with the dual of a finitely presented module. -/
def dualBaseChangeEquiv [Module.Flat R S] [Module.FinitePresentation R M] :
    S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) :=
  (Module.FinitePresentation.isBaseChange_map R M R S).equiv ≪≫ₗ
    (AlgebraTensorModule.rid R S S).congrRight

@[simp]
theorem dualBaseChangeEquiv_tmul [Module.Flat R S] [Module.FinitePresentation R M]
    (s t : S) (φ : Module.Dual R M) (m : M) :
    dualBaseChangeEquiv R S M (s ⊗ₜ[R] φ) (t ⊗ₜ[R] m) =
      s * t * algebraMap R S (φ m) := by
  simp [dualBaseChangeEquiv, LinearEquiv.congrRight, LinearEquiv.arrowCongr,
    IsBaseChange.equiv_tmul, Algebra.smul_def, mul_assoc, mul_comm]

/-- Over the cover, the original contraction becomes the invertible
module's evaluation isomorphism after the canonical tensor identifications. -/
def evaluationAfterBaseChangeEquiv
    [Module.Flat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)] :
    S ⊗[R] (Module.Dual R M ⊗[R] M) ≃ₗ[S] S :=
  AlgebraTensorModule.distribBaseChange R S (Module.Dual R M) M ≪≫ₗ
    TensorProduct.congr (dualBaseChangeEquiv R S M) (LinearEquiv.refl S (S ⊗[R] M)) ≪≫ₗ
    Module.Invertible.linearEquiv S (S ⊗[R] M)

@[simp]
theorem evaluationAfterBaseChangeEquiv_tmul
    [Module.Flat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)]
    (s : S) (φ : Module.Dual R M) (m : M) :
    evaluationAfterBaseChangeEquiv R S M (s ⊗ₜ[R] (φ ⊗ₜ[R] m)) =
      s * algebraMap R S (φ m) := by
  simp [evaluationAfterBaseChangeEquiv, Module.Invertible.linearEquiv]

/-- The base-changed contraction is the evaluation equivalence. -/
theorem evaluationAfterBaseChange_eq
    [Module.Flat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)] :
    (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S S (contractLeft R M) =
        (evaluationAfterBaseChangeEquiv R S M).toLinearMap := by
  ext φ m
  simp [Algebra.smul_def]

/-- Invertibility of finitely presented modules descends along faithfully
flat ring maps. This asserts invertibility of the actual evaluation map. -/
theorem invertible_of_faithfullyFlat_baseChange
    [Module.FaithfullyFlat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)] : Module.Invertible R M := by
  constructor
  let c : (Module.Dual R M ⊗[R] M) →ₗ[R] R := {
    toFun := contractLeft R M
    map_add' := (contractLeft R M).map_add
    map_smul' := (contractLeft R M).map_smul
  }
  change Function.Bijective c
  have hreflect := @Module.FaithfullyFlat.lTensor_bijective_iff_bijective
    R S inferInstance inferInstance inferInstance
    (Module.Dual R M ⊗[R] M) R inferInstance inferInstance inferInstance inferInstance
    c inferInstance
  apply hreflect.mp
  have heq := evaluationAfterBaseChange_eq R S M
  have heval := (evaluationAfterBaseChangeEquiv R S M).bijective
  let F := AlgebraTensorModule.lTensor S S (contractLeft R M)
  let e := AlgebraTensorModule.rid R S S
  have hcomp (x : S ⊗[R] (Module.Dual R M ⊗[R] M)) :
      e (F x) = evaluationAfterBaseChangeEquiv R S M x :=
    LinearMap.congr_fun heq x
  change Function.Bijective F
  constructor
  · intro x y hxy
    apply heval.1
    rw [← hcomp x, ← hcomp y]
    exact congrArg e hxy
  · intro y
    obtain ⟨x, hx⟩ := heval.2 (e y)
    refine ⟨x, e.injective ?_⟩
    rw [hcomp x]
    exact hx

/-- On noetherian affine schemes, no finite-presentation hypothesis on
the descended module is needed: it follows by faithful flat descent of
finite generation. -/
theorem invertible_of_faithfullyFlat_baseChange_noetherian
    [IsNoetherianRing R] [Module.FaithfullyFlat R S]
    [Module.Invertible S (S ⊗[R] M)] : Module.Invertible R M := by
  have : Module.Finite R M :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact invertible_of_faithfullyFlat_baseChange R S M

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent
