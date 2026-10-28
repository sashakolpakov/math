import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.MonomialMatrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.CokernelLocalization
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Cokernel Relabeling -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CokernelRelabeling

noncomputable section

/-! Relabeling a configuration gives an actual linear equivalence of
its evaluation cokernels. Flatness and all stalk ranks are preserved,
including when the two finite label sets lie in different universes. -/
universe u v w z
variable {R : Type u} [CommRing R]

def linearCokernelCodomainEquiv
    {V : Type v} [AddCommGroup V] [Module R V]
    {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (f : V →ₗ[R] M) (g : V →ₗ[R] N)
    (h : e.toLinearMap.comp f = g) : (M ⧸ f.range) ≃ₗ[R] (N ⧸ g.range) :=
  Submodule.Quotient.equiv f.range g.range e (by
    rw [← LinearMap.range_comp, h])

def configurationRowEquiv {ι : Type v} {κ : Type w} (e : κ ≃ ι) :
    (ι → R) ≃ₗ[R] (κ → R) where
  toFun x c := x (e c)
  invFun y c := y (e.symm c)
  left_inv x := by funext c; exact congrArg x (e.apply_symm_apply c)
  right_inv y := by funext c; exact congrArg y (e.symm_apply_apply c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def configurationEvaluationCokernelRelabelEquiv
    {ι : Type v} {κ : Type w} {n : ℕ}
    (w : ι → Fin (n + 1) → R) (d : ℕ) (e : κ ≃ ι) :
    ((ι → R) ⧸ (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d).range) ≃ₗ[R]
      ((κ → R) ⧸ (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c => w (e c)) d).range) :=
  linearCokernelCodomainEquiv (configurationRowEquiv e)
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d)
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c => w (e c)) d) rfl

def configurationMatrixCokernelRelabelEquiv
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {n : ℕ} (w : ι → Fin (n + 1) → R) (d : ℕ) (e : κ ≃ ι) :
    ((ι → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w d)).range) ≃ₗ[R]
      ((κ → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix (fun c => w (e c)) d)).range) :=
  (Submodule.quotEquivOfEq _ _ (MonomialMatrix.configurationMonomialMatrix_range w)).trans
    ((configurationEvaluationCokernelRelabelEquiv w d e).trans
      (Submodule.quotEquivOfEq _ _ (MonomialMatrix.configurationMonomialMatrix_range (fun c => w (e c))).symm))

theorem configurationMonomialMatrix_flatRank_relabel_iff
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {n : ℕ} (w : ι → Fin (n + 1) → R) (d k m : ℕ) (e : κ ≃ ι) :
    (Module.Flat R ((κ → R) ⧸
        (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix (fun c => w (e c)) d)).range) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
        ((κ → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix (fun c => w (e c)) d)).range) p + k = m) ↔
    (Module.Flat R ((ι → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w d)).range) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
        ((ι → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w d)).range) p + k = m) := by
  let E := configurationMatrixCokernelRelabelEquiv w d e
  have h := Module.rankAtStalk_eq_of_equiv E
  constructor
  · rintro ⟨hflat, hrank⟩
    let := hflat
    refine ⟨Module.Flat.of_linearEquiv E, fun p => ?_⟩
    rw [congrFun h p]
    exact hrank p
  · rintro ⟨hflat, hrank⟩
    let := hflat
    refine ⟨Module.Flat.of_linearEquiv E.symm, fun p => ?_⟩
    rw [← congrFun h p]
    exact hrank p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CokernelRelabeling
