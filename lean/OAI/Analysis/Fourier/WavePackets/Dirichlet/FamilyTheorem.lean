import OAI.Analysis.Fourier.WavePackets.General.Family.Regularity
import OAI.Analysis.Fourier.WavePackets.General.Family.Barriers
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Theorem

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {P V ι : Type*} {m s : ℕ}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {slots : Fin s → Quaternion ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}

/-- Joint smoothness up to the moving boundary, expressed by actual
smooth local representatives, rather than by a regularity assumption. -/
def DirichletFamilySmoothUpToBoundary
    (D : Z → PeriodicQuaternionicData slots e b) (A : Set Z)
    (S : DirichletSolutionFamily D) : Prop :=
  ∀ z ∈ A, ∀ x, (D z).defining x ≤ 0 →
    ∃ O : Set (Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s), IsOpen O ∧ (z,x) ∈ O ∧
      ∃ u : Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ, ContDiffOn ℝ ∞ u O ∧
        ∀ p ∈ O, p.1 ∈ A → (D p.1).defining p.2 ≤ 0 → u p = (S p.1).u p.2

/-- The barrier constants are chosen uniformly on a parameter
neighborhood and before any solution is selected. -/
def DirichletFamilyUniformBarriers
    (D : Z → PeriodicQuaternionicData slots e b) (A : Set Z) : Prop :=
  ∀ z₀ ∈ A, ∃ r B c : ℝ, 0 < r ∧ closedBall z₀ r ⊆ A ∧
    0 < c ∧ c ≤ B ∧ ∀ z ∈ closedBall z₀ r,
      ∀ S : PeriodicQuaternionicSolution (D z), ∀ x, (D z).defining x ≤ 0 →
        B*(D z).defining x ≤ S.u x ∧ S.u x ≤ c*(D z).defining x

/-- The complete four-slot smooth-family Dirichlet theorem. Existence,
joint boundary smoothness, uniqueness and locally uniform barriers follow
from the original data and genuine local closure diffeomorphisms. -/
theorem fourSlot_periodic_quaternionic_dirichlet_family
    [FiniteDimensional ℝ Z] [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V}
    {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {A : Set Z}
    (hD : LocallyTrivialDirichletData D A) :
    (∃ S : DirichletSolutionFamily D, DirichletFamilySmoothUpToBoundary D A S ∧
      ∀ z ∈ A, ∀ T : PeriodicQuaternionicSolution (D z), ∀ x,
        (D z).defining x ≤ 0 → T.u x = (S z).u x) ∧
      DirichletFamilyUniformBarriers D A := by
  constructor
  · obtain ⟨S,hS⟩ := exists_smooth_periodic_dirichlet_family hD
    exact ⟨S,hS,fun z _ T => T.eq_on_closed (S z)⟩
  · intro z₀ hz₀
    obtain ⟨U,hUA,⟨G⟩⟩ := hD.2 z₀ hz₀
    obtain ⟨r,B,c,hr,hU,hc,hcB,hbar⟩ := G.locally_uniform_barriers
    exact ⟨r,B,c,hr,hU.trans hUA,hc,hcB,hbar⟩

end OAI.Analysis.Fourier.WavePackets
