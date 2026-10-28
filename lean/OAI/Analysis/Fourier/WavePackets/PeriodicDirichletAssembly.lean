import OAI.Analysis.Fourier.WavePackets.PeriodicDirichlet

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff ComplexOrder

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}

/-- Finite dimensionality of the transverse factor follows from the given
coordinate splitting; it is not an additional hypothesis on the data. -/
theorem finiteDimensional_transverse_of_split
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V) : FiniteDimensional ℝ V := by
  let T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 →ₗ[ℝ] V :=
    (LinearMap.snd ℝ P V).comp e.toLinearEquiv.toLinearMap
  apply FiniteDimensional.of_surjective T
  intro v
  obtain ⟨x, hx⟩ := e.surjective (0, v)
  exact ⟨x, congrArg Prod.snd hx⟩

/-- Convert an actual smooth solution for the full potential to the
zero-boundary correction used in the periodic Dirichlet theorem. -/
def PeriodicQuaternionicData.solutionOfPotential
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b)
    (ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b ψ)
    (hb : ∀ x, D.defining x = 0 → ψ x = D.background x)
    (hpos : ∀ x, D.defining x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x, D.defining x ≤ 0 →
      OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = D.density x) :
    PeriodicQuaternionicSolution D where
  u := ψ - D.background
  smooth := hψ.sub D.background_smooth
  periodic := by
    intro x l
    change ψ _ - D.background _ = ψ x - D.background x
    rw [hp x l, D.background_periodic x l]
  boundary := by
    intro x hx
    exact sub_eq_zero.mpr (hb x hx)
  admissible := by
    have h : (fun y => D.background y + (ψ - D.background) y) = ψ := by
      funext y
      simp
    intro x hx
    rw [h]
    exact hpos x hx.le
  equation := by
    have h : (fun y => D.background y + (ψ - D.background) y) = ψ := by
      funext y
      simp
    intro x hx
    rw [h]
    exact heq x hx.le

/-- An empty closed fiber imposes no equation or boundary values. -/
def PeriodicQuaternionicData.solutionOfEmpty
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b)
    (hD : ¬ {x | D.defining x ≤ 0}.Nonempty) :
    PeriodicQuaternionicSolution D where
  u := 0
  smooth := contDiff_const
  periodic := by intro x l; rfl
  boundary := by intro x hx; rfl
  admissible := by
    intro x hx
    exact (hD ⟨x, hx.le⟩).elim
  equation := by
    intro x hx
    exact (hD ⟨x, hx.le⟩).elim

/-- The smooth extensions outside the fiber need not agree, but the
Dirichlet solution is unique on the entire closed fiber. -/
theorem PeriodicQuaternionicSolution.eq_on_closed
    {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b}
    (S T : PeriodicQuaternionicSolution D) :
    ∀ x, D.defining x ≤ 0 → S.u x = T.u x := by
  have he := OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_uniqueness_continuous_lattice D.dimension e b D.compact
    ((D.background_smooth.add S.smooth).of_le (by simp)).contDiffOn
    ((D.background_smooth.add T.smooth).of_le (by simp)).contDiffOn
    (D.defining_smooth.of_le (by simp))
    (D.background_smooth.continuous.add S.smooth.continuous).continuousOn
    (D.background_smooth.continuous.add T.smooth.continuous).continuousOn
    D.bounded D.defining_periodic
    (D.background_periodic.add S.periodic) (D.background_periodic.add T.periodic)
    (fun x hx => D.defining_positive x hx.le) S.admissible T.admissible
    (fun x hx => (S.equation x hx).trans (T.equation x hx).symm)
    (fun x hx => by simp only [S.boundary x hx, T.boundary x hx])
  intro x hx
  exact add_left_cancel (he x hx)

end OAI.Analysis.Fourier.WavePackets
