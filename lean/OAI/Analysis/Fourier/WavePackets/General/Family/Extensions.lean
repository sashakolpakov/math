import OAI.Analysis.Fourier.WavePackets.General.Family.Coefficients
import OAI.Analysis.PDE.Dirichlet.CalculusLocalFamilyCoefficients

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff

variable {Z P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

structure SmoothFamilyCoefficients (G : LocalDirichletFamily D z₀ U) (T : Set Z) where
  jacobian : Z × E → E →L[ℝ] E
  curvature : Z × E → E →L[ℝ] E →L[ℝ] E
  background : Z × E → E →L[ℝ] E →L[ℝ] ℝ
  source : Z × E → ℝ
  jacobian_smooth : ContDiff ℝ ∞ jacobian
  curvature_smooth : ContDiff ℝ ∞ curvature
  background_smooth : ContDiff ℝ ∞ background
  source_smooth : ContDiff ℝ ∞ source
  jacobian_periodic : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => jacobian (z,x))
  curvature_periodic : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => curvature (z,x))
  background_periodic : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => background (z,x))
  source_periodic : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => source (z,x))
  exact_germs : ∀ z ∈ T, ∀ x, (D z₀).defining x ≤ 0 →
    jacobian =ᶠ[𝓝 (z,x)] G.rawJacobian ∧
    curvature =ᶠ[𝓝 (z,x)] G.rawCurvature ∧
    background =ᶠ[𝓝 (z,x)] G.rawBackground ∧
    source =ᶠ[𝓝 (z,x)] G.rawSource

theorem LocalDirichletFamily.rawJacobian_smooth
    (G : LocalDirichletFamily D z₀ U) :
    ContDiffOn ℝ ∞ G.rawJacobian G.sourceNeighborhood :=
  OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiffOn_localFamilyJacobian G.target_open G.forward_smooth G.backward_smooth
    (fun p hp => G.forward_mem p hp)

theorem LocalDirichletFamily.rawCurvature_smooth
    (G : LocalDirichletFamily D z₀ U) :
    ContDiffOn ℝ ∞ G.rawCurvature G.sourceNeighborhood :=
  OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiffOn_localFamilyCurvature G.target_open G.forward_smooth G.backward_smooth
    (fun p hp => G.forward_mem p hp)

theorem LocalDirichletFamily.rawBackground_smooth
    (G : LocalDirichletFamily D z₀ U) :
    ContDiffOn ℝ ∞ G.rawBackground G.sourceNeighborhood :=
  OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiffOn_localFamilyBackground G.target_open G.forward_smooth G.background_smooth
    (fun p hp => G.forward_mem p hp)

theorem LocalDirichletFamily.rawSource_smooth
    (G : LocalDirichletFamily D z₀ U) :
    ContDiffOn ℝ ∞ G.rawSource G.sourceNeighborhood :=
  G.density_smooth.comp (contDiffOn_fst.prodMk G.forward_smooth)
    (fun p hp => G.forward_mem p hp)

/-- The genuine local geometry constructs all four globally smooth,
periodic coefficient fields. No extension or coefficient regularity is
assumed. They retain the joint germ at every closed source-fiber point. -/
theorem LocalDirichletFamily.nonempty_smoothFamilyCoefficients
    [FiniteDimensional ℝ Z] [FiniteDimensional ℝ P]
    (G : LocalDirichletFamily D z₀ U) {T : Set Z} (hT : IsCompact T) (hTU : T ⊆ U) :
    Nonempty (SmoothFamilyCoefficients G T) := by
  have hCU (z : Z) (hz : z ∈ T) (x : E) (hx : (e x).2 ∈ G.referenceClosure) :
      (z,x) ∈ G.sourceNeighborhood :=
    G.source_closed ⟨hTU hz,(G.mem_referenceClosure_iff x).mp hx⟩
  obtain ⟨J,hJ,hJp,hJe⟩ := exists_smooth_parameter_lattice_extension e b hT
    G.isCompact_referenceClosure G.source_open hCU G.rawJacobian G.rawJacobian_smooth
    G.rawJacobian_periodic
  obtain ⟨K,hK,hKp,hKe⟩ := exists_smooth_parameter_lattice_extension e b hT
    G.isCompact_referenceClosure G.source_open hCU G.rawCurvature G.rawCurvature_smooth
    G.rawCurvature_periodic
  obtain ⟨B,hB,hBp,hBe⟩ := exists_smooth_parameter_lattice_extension e b hT
    G.isCompact_referenceClosure G.source_open hCU G.rawBackground G.rawBackground_smooth
    G.rawBackground_periodic
  obtain ⟨F,hF,hFp,hFe⟩ := exists_smooth_parameter_lattice_extension e b hT
    G.isCompact_referenceClosure G.source_open hCU G.rawSource G.rawSource_smooth
    G.rawSource_periodic
  refine ⟨⟨J,K,B,F,hJ,hK,hB,hF,hJp,hKp,hBp,hFp,?_⟩⟩
  intro z hz x hx
  have hc := (G.mem_referenceClosure_iff x).mpr hx
  exact ⟨hJe z hz x hc,hKe z hz x hc,hBe z hz x hc,hFe z hz x hc⟩

end OAI.Analysis.Fourier.WavePackets
