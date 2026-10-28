import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
import OAI.RepresentationTheory.Hecke.RadialDilation.EighthPhaseSubgroup

/-! # Finite Phase Image -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization

noncomputable section

/-! Eighth-root stabilization depends only on the projected finite symplectic matrix. -/

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def finiteEighthPhaseImage (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) : Subgroup (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) :=
  (EighthPhaseSubgroup.Realization.eighthPhaseStabilizer D.finite.action f).map D.finite.project

theorem finite_eighth_phase_of_projection_mem (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (m : MpF) (hm : D.finite.project m ∈ finiteEighthPhaseImage D f) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ D.finite.action m f = ξ • f := by
  obtain ⟨u, ⟨ζ, hζ, huf⟩, hu⟩ := hm
  obtain ⟨ε, hε, ha⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D m u hu.symm
  have hε8 : ε ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
  refine ⟨ε * ζ, by rw [mul_pow, hε8, hζ, mul_one], ?_⟩
  rw [ha, huf, smul_smul]

theorem finite_projection_mem_phase_image (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (m : MpF) (ξ : ℂ) (hξ : ξ ^ 8 = 1)
    (hf : D.finite.action m f = ξ • f) : D.finite.project m ∈ finiteEighthPhaseImage D f :=
  ⟨m, ⟨ξ, hξ, hf⟩, rfl⟩

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization
