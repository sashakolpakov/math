import OAI.Analysis.HodgeTheory.Decomposition.CompactInclusion
import OAI.Analysis.HodgeTheory.Decomposition.WeakResolvent
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactEnergy
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import OAI.Analysis.HodgeTheory.Decomposition.CompactIsometry

/-! # Weak Harmonics -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakHarmonics.Constructions

noncomputable section

/-! The actual weak harmonic kernel is finite dimensional. Orthogonal
projection yields the weak harmonic component of every genuine L² form. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

abbrev ProjectiveWeakHarmonics := (EnergyDomain.Constructions.projectiveEnergyDerivative V n).ker

instance projectiveWeakHarmonics_innerProductSpace : InnerProductSpace ℂ (ProjectiveWeakHarmonics V n) :=
  @Submodule.innerProductSpace ℂ (EnergyDomain.Constructions.ProjectiveEnergyDomain V n) _ _ _ (ProjectiveWeakHarmonics V n)

instance projectiveWeakHarmonics_complete : CompleteSpace (ProjectiveWeakHarmonics V n) :=
  (EnergyDomain.Constructions.projectiveEnergyDerivative V n).isClosed_ker.completeSpace_coe

def projectiveWeakHarmonicInclusion : ProjectiveWeakHarmonics V n →L[ℂ] Form.Constructions.ProjectiveL2Forms V (n + 1) :=
  (EnergyDomain.Constructions.projectiveEnergyInclusion V n).comp (ProjectiveWeakHarmonics V n).subtypeL

theorem projectiveWeakHarmonicInclusion_inner (u v : ProjectiveWeakHarmonics V n) :
    inner ℂ (projectiveWeakHarmonicInclusion V n u) (projectiveWeakHarmonicInclusion V n v) =
      inner ℂ u v := by
  have h := EnergyDomain.Constructions.projectiveEnergyDomain_inner V n u.val v.val
  rw [show EnergyDomain.Constructions.projectiveEnergyDerivative V n u.val = 0 from u.property, inner_zero_left, add_zero] at h
  exact h.symm

theorem projectiveWeakHarmonics_finiteDimensional : FiniteDimensional ℂ (ProjectiveWeakHarmonics V n) := by
  exact CompactIsometry.Constructions.finiteDimensional_of_compact_inner_preserving
    (E := ProjectiveWeakHarmonics V n) (F := Form.Constructions.ProjectiveL2Forms V (n + 1))
    (projectiveWeakHarmonicInclusion V n)
    ((CompactInclusion.Constructions.projectiveEnergyInclusion_isCompact V n).comp_clm (ProjectiveWeakHarmonics V n).subtypeL)
    (projectiveWeakHarmonicInclusion_inner V n)

def projectiveWeakHarmonicPart (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) : ProjectiveWeakHarmonics V n :=
  (InnerProductSpace.toDual ℂ (ProjectiveWeakHarmonics V n)).symm
    ((innerSL ℂ f).comp (projectiveWeakHarmonicInclusion V n))

theorem projectiveWeakHarmonicPart_pair (f : Form.Constructions.ProjectiveL2Forms V (n + 1))
    (k : ProjectiveWeakHarmonics V n) :
    inner ℂ (projectiveWeakHarmonicInclusion V n (projectiveWeakHarmonicPart V n f))
      (projectiveWeakHarmonicInclusion V n k) =
        inner ℂ f (projectiveWeakHarmonicInclusion V n k) := by
  rw [projectiveWeakHarmonicInclusion_inner]
  exact InnerProductSpace.toDual_symm_apply

theorem projectiveWeakHarmonicPart_remainder_orthogonal (f : Form.Constructions.ProjectiveL2Forms V (n + 1))
    (k : ProjectiveWeakHarmonics V n) :
    inner ℂ (f - projectiveWeakHarmonicInclusion V n (projectiveWeakHarmonicPart V n f))
      (projectiveWeakHarmonicInclusion V n k) = 0 := by
  rw [inner_sub_left, projectiveWeakHarmonicPart_pair, sub_self]

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakHarmonics.Constructions
