import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.LocalProperties.Exactness

/-! # Local Invertibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.LocalInvertibility

noncomputable section

/-!
# Zariski-local invertibility of modules for PoincareBundle

Invertibility is checked on a principal-open cover by testing the actual
evaluation map after localization. The finite-presentation hypothesis
needed to commute duals with localization follows from the same cover.
-/

open TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- The evaluation map becomes bijective after flat base change to a ring
over which the module is invertible. -/
theorem baseChangedContraction_bijective
    [Module.Flat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)] :
    Function.Bijective (AlgebraTensorModule.lTensor S S (contractLeft R M)) := by
  let F := AlgebraTensorModule.lTensor S S (contractLeft R M)
  let e := AlgebraTensorModule.rid R S S
  have heval := (Affine.LineDescent.evaluationAfterBaseChangeEquiv R S M).bijective
  have hcomp (x : S ⊗[R] (Module.Dual R M ⊗[R] M)) :
      e (F x) = Affine.LineDescent.evaluationAfterBaseChangeEquiv R S M x :=
    LinearMap.congr_fun (Affine.LineDescent.evaluationAfterBaseChange_eq R S M) x
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

/-- A module that is invertible on a principal-open cover is invertible. -/
theorem invertible_of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (hloc : ∀ r : s,
      Module.Invertible (Localization.Away r.1) (LocalizedModule.Away r.1 M)) :
    Module.Invertible R M := by
  have : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan s hs (fun r => by
      have := hloc r
      exact Module.finitePresentation_of_projective _ _)
  constructor
  let c : (Module.Dual R M ⊗[R] M) →ₗ[R] R := {
    toFun := contractLeft R M
    map_add' := (contractLeft R M).map_add
    map_smul' := (contractLeft R M).map_smul
  }
  change Function.Bijective c
  apply bijective_of_isLocalized_span s hs
    (fun r => Localization.Away r.1 ⊗[R] (Module.Dual R M ⊗[R] M))
    (fun r => TensorProduct.mk R (Localization.Away r.1) _ 1)
    (fun r => Localization.Away r.1 ⊗[R] R)
    (fun r => TensorProduct.mk R (Localization.Away r.1) R 1) c
  intro r
  have := hloc r
  have : Module.Invertible (Localization.Away r.1) (Localization.Away r.1 ⊗[R] M) :=
    Module.Invertible.congr
      (IsLocalizedModule.isBaseChange (.powers r.1) (Localization.Away r.1)
        (LocalizedModule.mkLinearMap (.powers r.1) M)).equiv.symm
  have heq : IsLocalizedModule.map (.powers r.1)
      (TensorProduct.mk R (Localization.Away r.1) _ 1)
      (TensorProduct.mk R (Localization.Away r.1) R 1) c =
        (AlgebraTensorModule.lTensor (Localization.Away r.1)
          (Localization.Away r.1) c).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext (.powers r.1)
      (TensorProduct.mk R (Localization.Away r.1) _ 1)
      (TensorProduct.mk R (Localization.Away r.1) R 1)
    ext x y
    exact IsLocalizedModule.map_apply (.powers r.1)
      (TensorProduct.mk R (Localization.Away r.1) _ 1)
      (TensorProduct.mk R (Localization.Away r.1) R 1) c (x ⊗ₜ[R] y)
  rw [heq]
  exact baseChangedContraction_bijective R (Localization.Away r.1) M

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.LocalInvertibility
