import OAI.Analysis.PDE.Concentration.NullRotation
import OAI.Analysis.Calculus.Current.Coordinates

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Current

def nullIndexEquiv (d : ℕ) : Fin (d + 2) ≃ OAI.Analysis.Calculus.Current.Index d :=
  (finSuccEquiv (d + 1)).trans (Equiv.optionCongr (finSuccEquiv d))

@[simp] theorem nullIndexEquiv_zero (d : ℕ) : nullIndexEquiv d 0 = none := by
  simp [nullIndexEquiv]

@[simp] theorem nullIndexEquiv_one (d : ℕ) : nullIndexEquiv d 1 = some none := by
  change (Equiv.optionCongr (finSuccEquiv d)) (some 0) = some none
  simp

@[simp] theorem nullIndexEquiv_transverse (d : ℕ) (i : Fin d) :
    nullIndexEquiv d i.succ.succ = some (some i) := by
  simp [nullIndexEquiv]

def nullCoordinateProjection (d : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 →L[ℝ] OAI.Analysis.Calculus.Current.CurrentSpace d :=
  (ContinuousLinearMap.pi fun i => EuclideanSpace.proj ((nullIndexEquiv d).symm i, 0)).prod
    (ContinuousLinearMap.pi fun i =>
      Complex.ofRealCLM.comp (EuclideanSpace.proj ((nullIndexEquiv d).symm i, 1)) +
        Complex.I • Complex.ofRealCLM.comp (EuclideanSpace.proj ((nullIndexEquiv d).symm i, 2)))

theorem nullCoordinateProjection_real (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (i : OAI.Analysis.Calculus.Current.Index d) :
    (nullCoordinateProjection d x).1 i = x ((nullIndexEquiv d).symm i, 0) := rfl

theorem nullCoordinateProjection_imaginary (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (i : OAI.Analysis.Calculus.Current.Index d) :
    (nullCoordinateProjection d x).2 i =
      (x ((nullIndexEquiv d).symm i, 1) : ℂ) +
        Complex.I * (x ((nullIndexEquiv d).symm i, 2) : ℂ) := rfl

theorem nullCoordinateProjection_coordinateVector (d : ℕ) (i : Fin (d + 2)) (α : Fin 3) :
    nullCoordinateProjection d (OAI.Analysis.PDE.Dirichlet.coordinateVector (i, α)) =
      OAI.Analysis.Calculus.Current.currentDirection (nullIndexEquiv d i, α) := by
  apply Prod.ext
  · funext j
    rw [nullCoordinateProjection_real]
    fin_cases α <;> simp [OAI.Analysis.Calculus.Current.currentDirection, OAI.Analysis.PDE.Dirichlet.coordinateVector, PiLp.single_apply,
      Pi.single_apply, Prod.ext_iff, Equiv.symm_apply_eq]
  · funext j
    rw [nullCoordinateProjection_imaginary]
    fin_cases α <;> simp [OAI.Analysis.Calculus.Current.currentDirection, OAI.Analysis.PDE.Dirichlet.coordinateVector, PiLp.single_apply,
      Pi.single_apply, Prod.ext_iff, Equiv.symm_apply_eq, apply_ite]
    tauto

end OAI.Analysis.PDE.Concentration
