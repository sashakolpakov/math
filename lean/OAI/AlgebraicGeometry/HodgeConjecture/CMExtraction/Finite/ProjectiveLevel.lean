import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.ControlOpen
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.EigenlineStabilizer

/-! # Projective Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.ProjectiveLevel.TestTransport

noncomputable section

/-! Every retained nonzero integral periodic test has an open
symplectic projective stabilizer, proved from Heisenberg covariance. -/

open scoped Classical _root_.Matrix _root_.Topology

variable {I : Type*} [Fintype I] [DecidableEq I]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)

def finiteProjectiveStabilizer : Subgroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  (EigenlineStabilizer.TestTransport.eigenlineStabilizer D.finite.action φ).map D.finite.project

theorem finite_project_kernel_preserves_line :
    D.finite.project.ker ≤ EigenlineStabilizer.TestTransport.eigenlineStabilizer D.finite.action φ := by
  intro m hm
  rcases (D.finite.kernel m).mp hm with rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simpa using D.finite.genuine φ⟩

theorem finiteProjectiveStabilizer_mem (m : MpF) :
    D.finite.project m ∈ finiteProjectiveStabilizer D φ ↔
      ∃ c : ℂˣ, D.finite.action m φ = (c : ℂ) • φ := by
  change m ∈ ((EigenlineStabilizer.TestTransport.eigenlineStabilizer D.finite.action φ).map D.finite.project).comap
    D.finite.project ↔ _
  rw [Subgroup.comap_map_eq_self (finite_project_kernel_preserves_line D φ)]
  rfl

theorem finiteProjectiveStabilizer_isOpen
    (hφ : φ ≠ 0) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x,
      φ.val (u + x) = φ.val x) :
    IsOpen (finiteProjectiveStabilizer D φ : Set (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  apply (finiteProjectiveStabilizer D φ).isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset ((ControlOpen.TestTransport.finiteLatticeControl_isOpen (I := I) N hN).mem_nhds
    (ControlOpen.TestTransport.finiteLatticeControl_one N hN))
  intro g hg
  obtain ⟨m, rfl⟩ := D.finite.surjective g
  obtain ⟨c, hc⟩ := LatticeControl.TestTransport.finite_lattice_control_scalar D N hN m hg φ hsupport hperiod
  exact (finiteProjectiveStabilizer_mem D φ m).mpr
    ⟨Units.mk0 c (EigenlineStabilizer.TestTransport.scalar_ne_zero_of_equiv D.finite.action φ m hφ c hc), hc⟩

def finiteProjectiveLevel
    (hφ : φ ≠ 0) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x,
      φ.val (u + x) = φ.val x) : OpenSubgroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toSubgroup := finiteProjectiveStabilizer D φ
  isOpen' := finiteProjectiveStabilizer_isOpen D φ hφ hsupport N hN hperiod

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.ProjectiveLevel.TestTransport
