import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms

/-! # Singleton Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SingletonCoordinates

noncomputable section

/-! One-chart homogeneous Čech cochains are exactly tuples of homogeneous sections on the singleton charts. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech

universe u v w

def singletonFinsetEquiv (σ : Type u) [DecidableEq σ] : σ ≃ {s : Finset σ // s.card = 1} :=
  Equiv.ofBijective (fun i => ⟨{i}, Finset.card_singleton i⟩) (by
    constructor
    · intro i j h
      exact Finset.singleton_injective (congrArg Subtype.val h)
    · intro s
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp s.property
      exact ⟨i, Subtype.ext hi.symm⟩)

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)

def moduleCechOneTermEquiv (d : ℤ) : HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 1 ≃ₗ[R]
    ((i : σ) → HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ {i} d) :=
  (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := σ) R M ℳ d 1).trans
    (LinearEquiv.piCongrLeft R (fun s : {s : Finset σ // s.card = 1} =>
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s.val d) (singletonFinsetEquiv σ)).symm

theorem moduleCechOneTermEquiv_apply (d : ℤ) (f : HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 1) (i : σ) :
    (moduleCechOneTermEquiv R M ℳ d f i).val = f.val {i} := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SingletonCoordinates
