import OAI.Analysis.Fourier.WavePackets.Dirichlet.FamilyTheorem
import OAI.Analysis.Fourier.WavePackets.General.Family.Padding

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

/-- The manuscript's three-slot, finite-dimensional smooth-family
Dirichlet theorem. The dummy fourth coordinates are padded, solved and
then removed; independence and the descended equation are proved by
the fixed-fiber uniqueness theorem. -/
theorem periodic_quaternionic_dirichlet_family
    {Z P V ι : Type} {m : ℕ}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
    [Fintype ι] {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b} {A : Set Z}
    (hD : LocallyTrivialDirichletData D A) :
    (∃ S : DirichletSolutionFamily D, DirichletFamilySmoothUpToBoundary D A S ∧
      ∀ z ∈ A, ∀ T : PeriodicQuaternionicSolution (D z), ∀ x,
        (D z).defining x ≤ 0 → T.u x = (S z).u x) ∧
      DirichletFamilyUniformBarriers D A := by
  have hp := hD.padFourth
  obtain ⟨⟨S₄,hS₄,hu₄⟩,hbar₄⟩ := fourSlot_periodic_quaternionic_dirichlet_family hp
  let S : DirichletSolutionFamily D := fun z => (S₄ z).descend (D z)
  constructor
  · refine ⟨S,?_,fun z _ T => T.threeSlot_eq_on_closed (S z)⟩
    intro z hz x hx
    have hx₄ : (D z).padFourth.defining (insertFourth m x) ≤ 0 := by
      simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth,dropFourth_insertFourth] using hx
    obtain ⟨O,hO,hpO,u,hu,hue⟩ := hS₄ z hz (insertFourth m x) hx₄
    let I : Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 → Z × OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 :=
      fun p => (p.1,insertFourth m p.2)
    have hI : ContDiff ℝ ∞ I := contDiff_fst.prodMk ((insertFourth m).contDiff.comp contDiff_snd)
    refine ⟨I ⁻¹' O,hO.preimage hI.continuous,hpO,fun p => u (I p),
      hu.comp hI.contDiffOn (fun _ h => h),?_⟩
    intro p hp hpA hpx
    have hpx₄ : (D p.1).padFourth.defining (insertFourth m p.2) ≤ 0 := by
      simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth,dropFourth_insertFourth] using hpx
    exact hue (I p) hp hpA hpx₄
  · intro z₀ hz₀
    obtain ⟨r,B,c,hr,hA,hc,hcB,hbar⟩ := hbar₄ z₀ hz₀
    refine ⟨r,B,c,hr,hA,hc,hcB,?_⟩
    intro z hz T x hx
    have h := hbar z hz T.padFourth (insertFourth m x)
      (by simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth,dropFourth_insertFourth] using hx)
    simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth,OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicSolution.padFourth,
      dropFourth_insertFourth] using h

end OAI.Analysis.Fourier.WavePackets
