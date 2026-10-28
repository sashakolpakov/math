import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.PolynomialSubstitution
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift

/-! # Cover Module -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverModule.ProjectiveCech

noncomputable section

/-! Actual Čech complexes of finite polynomial covers, using the polynomial action given by evaluation. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.PolynomialSubstitution.GradedModules

universe u v w t z

variable {σ : Type u} (R : Type v) [CommRing R]

section General

variable (A : Type w) [CommRing A] [Algebra R A]
variable (M : Type t) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

@[instance_reducible]
def polynomialCoverModule (a : σ → A) : Module (MvPolynomial σ R) M :=
  Module.compHom M (MvPolynomial.aeval a).toRingHom

theorem polynomialCover_scalarTower (a : σ → A) :
    let := polynomialCoverModule R A M a
    IsScalarTower R (MvPolynomial σ R) M := by
  let := polynomialCoverModule R A M a
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change MvPolynomial.aeval a (C r) • m = r • m
  rw [MvPolynomial.aeval_C, algebraMap_smul A]

variable [LinearOrder σ]

def polynomialCoverCechExactAt (a : σ → A) (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ) : Prop :=
  let := polynomialCoverModule R A M a
  let := polynomialCover_scalarTower R A M a
  Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q

end General

section Composition

variable {κ : Type z}
variable (A : Type w) [CommRing A] [Algebra R A]
variable (M : Type t) [AddCommGroup M] [Module A M]

theorem polynomialCover_composition_tower (a : σ → A) (b : κ → A)
    (f : MvPolynomial κ R →ₐ[R] MvPolynomial σ R)
    (hf : (MvPolynomial.aeval a).comp f = MvPolynomial.aeval b) :
    let := f.toRingHom.toAlgebra
    let := polynomialCoverModule R A M a
    let := polynomialCoverModule R A M b
    IsScalarTower (MvPolynomial κ R) (MvPolynomial σ R) M := by
  let := f.toRingHom.toAlgebra
  let := polynomialCoverModule R A M a
  let := polynomialCoverModule R A M b
  apply IsScalarTower.of_algebraMap_smul
  intro p m
  change MvPolynomial.aeval a (f p) • m = MvPolynomial.aeval b p • m
  exact congrArg (fun r : A => r • m) (DFunLike.congr_fun hf p)

end Composition

variable {τ : Type w} [Fintype σ] [Fintype τ]
variable (M : Type t) [AddCommGroup M] [Module R M] [Module (MvPolynomial τ R) M]
  [IsScalarTower R (MvPolynomial τ R) M]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := τ) R) ℳ]

omit [IsScalarTower R (MvPolynomial τ R) M] in
theorem polynomialCover_gradedSMul (a : σ → MvPolynomial τ R) (ha : ∀ i, (a i).IsHomogeneous 1) :
    let := polynomialCoverModule R (MvPolynomial τ R) M a
    SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ := by
  let := polynomialCoverModule R (MvPolynomial τ R) M a
  constructor
  intro i j p m hp hm
  change (MvPolynomial.aeval a p) • m ∈ ℳ (i +ᵥ j)
  exact SetLike.GradedSMul.smul_mem (Linear.PolynomialSubstitution.GradedModules.linearSubstitution_integer_homogeneous R a ha hp) hm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverModule.ProjectiveCech
