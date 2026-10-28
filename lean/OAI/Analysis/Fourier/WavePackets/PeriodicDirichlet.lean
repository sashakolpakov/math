import OAI.Analysis.Fourier.WavePackets.DummyIndependence

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff ComplexOrder

/-- Fixed-fiber data for the manuscript's periodic quaternionic Dirichlet
theorem. Only the transverse closure is compact; no compactness of the
lifted periodic domain is imposed. -/
structure PeriodicQuaternionicData {m s : ℕ} (slots : Fin s → Quaternion ℝ)
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s ≃L[ℝ] P × V) (b : Basis ι ℝ P) where
  dimension : 1 ≤ m
  defining : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ
  background : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ
  density : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ
  transverse : Set V
  compact : IsCompact transverse
  bounded : ∀ x, defining x ≤ 0 → (e x).2 ∈ transverse
  defining_smooth : ContDiff ℝ ∞ defining
  background_smooth : ContDiff ℝ ∞ background
  density_smooth : ContDiff ℝ ∞ density
  defining_periodic : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b defining
  background_periodic : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b background
  density_periodic : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b density
  regular : ∀ x, defining x = 0 → fderiv ℝ defining x ≠ 0
  defining_positive : ∀ x, defining x ≤ 0 →
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots defining x)).PosDef
  background_nonnegative : ∀ x, defining x ≤ 0 →
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots background x)).PosSemidef
  background_degenerate : ∀ x, defining x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots background x) = 0
  density_positive : ∀ x, defining x ≤ 0 → 0 < density x

/-- A genuine smooth solution, not an assumed estimate. Global spatial
smoothness merely chooses an extension of the smooth germ near the closed
fiber; it asserts no smoothness across a time-parameter endpoint. -/
structure PeriodicQuaternionicSolution {m s : ℕ} {slots : Fin s → Quaternion ℝ}
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (D : PeriodicQuaternionicData slots e b) where
  u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ
  smooth : ContDiff ℝ ∞ u
  periodic : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u
  boundary : ∀ x, D.defining x = 0 → u x = 0
  admissible : ∀ x, D.defining x < 0 →
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => D.background y + u y) x)).PosDef
  equation : ∀ x, D.defining x < 0 →
    OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => D.background y + u y) x) = D.density x

/-- The general four-slot theorem to be supplied by the continuity method.
The data are arbitrary smooth periodic data, not packet-specific estimates.
The nontrivial transverse factor includes the manuscript's real transverse
dimension `2m` for `m ≥ 1`. -/
def FourSlotDirichletExistence : Prop :=
  ∀ (m : ℕ) (P V ι : Type)
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] [Fintype ι]
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b), Nonempty (PeriodicQuaternionicSolution D)

theorem PeriodicQuaternionicSolution.nonpositive {m : ℕ}
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} (S : PeriodicQuaternionicSolution D) :
    ∀ x, D.defining x ≤ 0 → S.u x ≤ 0 := by
  have hc := OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_comparison_continuous_lattice D.dimension e b D.compact
    ((D.background_smooth.add S.smooth).of_le (by simp)).contDiffOn
    (D.background_smooth.of_le (by simp)).contDiffOn (D.defining_smooth.of_le (by simp))
    (D.background_smooth.continuous.add S.smooth.continuous).continuousOn
    D.background_smooth.continuous.continuousOn D.bounded D.defining_periodic
    (D.background_periodic.add S.periodic) D.background_periodic
    (fun x hx => D.defining_positive x hx.le) S.admissible
    (fun x hx => by rw [S.equation x hx, D.background_degenerate x hx.le]; exact (D.density_positive x hx.le).le)
    (fun x hx => by simp only [S.boundary x hx, add_zero, le_refl])
  intro x hx
  have h := hc x hx
  linarith

end OAI.Analysis.Fourier.WavePackets
