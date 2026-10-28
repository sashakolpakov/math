import OAI.Analysis.PDE.Concentration.VectorExtension

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

variable {Z E P V F ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Move the parameter into the nonperiodic factor without changing any
spatial period. -/
def parameterLatticeSplit (e : E ≃L[ℝ] P × V) : (Z × E) ≃L[ℝ] P × (Z × V) where
  toFun p := ((e p.2).1, p.1, (e p.2).2)
  invFun p := (p.2.1, e.symm (p.1,p.2.2))
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp [Prod.mk_add_mk]
  map_smul' c p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem parameterLatticeSplit_apply (e : E ≃L[ℝ] P × V) (p : Z × E) :
    parameterLatticeSplit e p = ((e p.2).1, p.1, (e p.2).2) := rfl

theorem parameterLatticeSplit_symm (e : E ≃L[ℝ] P × V) (p : P × (Z × V)) :
    (parameterLatticeSplit e).symm p = (p.2.1, e.symm (p.1,p.2.2)) := rfl

theorem parameter_latticePeriodic_iff (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (f : Z × E → F) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (parameterLatticeSplit e) b f ↔
      ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (z,x)) := by
  constructor
  · intro hf z x l
    exact hf (z,x) l
  · intro hf p l
    exact hf p.1 p.2 l

/-- Compact-parameter, compact-transverse extension of local smooth
periodic coefficient fields. The extension preserves the full joint germ. -/
theorem exists_smooth_parameter_lattice_extension
    [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {T : Set Z} (hT : IsCompact T) {C : Set V} (hC : IsCompact C)
    {U : Set (Z × E)} (hU : IsOpen U)
    (hCU : ∀ z ∈ T, ∀ x, (e x).2 ∈ C → (z,x) ∈ U)
    (f : Z × E → F) (hf : ContDiffOn ℝ ∞ f U)
    (hfp : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (z,x))) :
    ∃ g : Z × E → F, ContDiff ℝ ∞ g ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => g (z,x))) ∧
      ∀ z ∈ T, ∀ x, (e x).2 ∈ C → g =ᶠ[𝓝 (z,x)] f := by
  obtain ⟨g, hg, hgp, hgf⟩ := OAI.Analysis.PDE.Concentration.exists_smooth_lattice_vector_extension_near
    (parameterLatticeSplit e) b (hT.prod hC) hU
    (fun p hp => hCU p.1 hp.1 p.2 hp.2) f hf
    ((parameter_latticePeriodic_iff e b f).mpr hfp)
  exact ⟨g, hg, (parameter_latticePeriodic_iff e b g).mp hgp,
    fun z hz x hx => hgf (z,x) ⟨hz,hx⟩⟩

end OAI.Analysis.Fourier.WavePackets
