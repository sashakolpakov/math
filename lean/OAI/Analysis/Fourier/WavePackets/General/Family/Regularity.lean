import OAI.Analysis.Fourier.WavePackets.General.Family.Boundary

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U A : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V] in
/-- A local smooth reference representative pushes forward to the actual
moving fibers using only the given local inverse coordinates. -/
theorem LocalDirichletFamily.pushforward_local_representative
    (G : LocalDirichletFamily D z₀ U) (S : DirichletSolutionFamily D)
    {x₀ : E} (hx₀ : (D z₀).defining x₀ ≤ 0)
    {O : Set (Z × E)} (hO : IsOpen O) (hpO : (z₀,x₀) ∈ O)
    {g : Z × E → ℝ} (hg : ContDiff ℝ ∞ g)
    (hge : ∀ p ∈ O, (D z₀).defining p.2 ≤ 0 → g p = G.referenceValue S p) :
    ∃ Q : Set (Z × E), IsOpen Q ∧ (z₀,x₀) ∈ Q ∧
      ∃ u : Z × E → ℝ, ContDiffOn ℝ ∞ u Q ∧
        ∀ p ∈ Q, (D p.1).defining p.2 ≤ 0 → u p = dirichletFamilyValue S p := by
  let H : Z × E → Z × E := fun p => (p.1,G.backward p)
  have hH : ContDiffOn ℝ ∞ H G.targetNeighborhood :=
    contDiffOn_fst.prodMk G.backward_smooth
  let Q := G.targetNeighborhood ∩ H ⁻¹' O
  have hQ : IsOpen Q := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hc : ContinuousAt H p :=
      ((hH p hp.1).contDiffAt (G.target_open.mem_nhds hp.1)).continuousAt
    exact Filter.inter_mem (G.target_open.mem_nhds hp.1)
      (hc.preimage_mem_nhds (hO.mem_nhds hp.2))
  have hp : (z₀,x₀) ∈ G.targetNeighborhood := G.target_closed ⟨G.base_mem,hx₀⟩
  have hself : H (z₀,x₀) = (z₀,x₀) := Prod.ext rfl (G.backward_base x₀ hp)
  refine ⟨Q,hQ,⟨hp,?_⟩,fun p => g (H p),hg.comp_contDiffOn (hH.mono inter_subset_left),?_⟩
  · change H (z₀,x₀) ∈ O
    rwa [hself]
  · intro p hp hpr
    have hpU : p.1 ∈ U := (G.target_parameter hp.1).1
    exact (hge (H p) hp.2 (G.backward_closed p.1 hpU p.2 hpr)).trans
      (G.referenceValue_inverse S hpU hpr)

/-- An arbitrary smooth finite-dimensional family of the original
Dirichlet data has genuine joint smoothness up to every moving boundary.
This conclusion is local on the parameter domain and makes no assertion
across a parameter endpoint or a degenerating fiber. -/
theorem LocallyTrivialDirichletData.local_smooth_representative
    (hD : LocallyTrivialDirichletData D A) (S : DirichletSolutionFamily D)
    {z : Z} (hz : z ∈ A) {x : E} (hx : (D z).defining x ≤ 0) :
    ∃ O : Set (Z × E), IsOpen O ∧ (z,x) ∈ O ∧
      ∃ u : Z × E → ℝ, ContDiffOn ℝ ∞ u O ∧
        ∀ p ∈ O, p.1 ∈ A → (D p.1).defining p.2 ≤ 0 →
          u p = dirichletFamilyValue S p := by
  rcases hx.eq_or_lt with heq | hlt
  · obtain ⟨U,hUA,⟨G⟩⟩ := hD.2 z hz
    obtain ⟨O,hO,hpO,g,hg,hge⟩ := G.referenceValue_local_boundary hUA hD S heq
    obtain ⟨Q,hQ,hpQ,u,hu,hue⟩ := G.pushforward_local_representative S hx hO hpO hg hge
    exact ⟨Q,hQ,hpQ,u,hu,fun p hp _ hpx => hue p hp hpx⟩
  · exact ⟨{p : Z × E | p.1 ∈ A ∧ (D p.1).defining p.2 < 0},
      hD.isOpen_movingInterior,⟨hz,hlt⟩,dirichletFamilyValue S,
      hD.value_contDiffOn_interior S,fun _ _ _ _ => rfl⟩

/-- The smooth-family clause includes existence; no family of solutions
or assumed smooth dependence is an input. -/
theorem exists_smooth_periodic_dirichlet_family
    (hD : LocallyTrivialDirichletData D A) :
    ∃ S : DirichletSolutionFamily D, ∀ z ∈ A, ∀ x, (D z).defining x ≤ 0 →
      ∃ O : Set (Z × E), IsOpen O ∧ (z,x) ∈ O ∧
        ∃ u : Z × E → ℝ, ContDiffOn ℝ ∞ u O ∧
          ∀ p ∈ O, p.1 ∈ A → (D p.1).defining p.2 ≤ 0 →
            u p = dirichletFamilyValue S p := by
  obtain ⟨S⟩ := nonempty_dirichletSolutionFamily D
  exact ⟨S,fun z hz x hx => hD.local_smooth_representative S hz hx⟩

end OAI.Analysis.Fourier.WavePackets
