import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentationFinite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Homogeneous Vector Space Basis -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousVectorSpaceBasis

noncomputable section

/-! A vector space with a direct-sum grading has a basis of homogeneous vectors. -/

open DirectSum
universe u v
variable {K : Type u} [Field K] {M : Type v} [AddCommGroup M] [Module K M]
variable (ℳ : ℤ → Submodule K M) [Decomposition ℳ]

def HomogeneousBasisIndex := Σ d : ℤ, Module.Free.ChooseBasisIndex K (ℳ d)

def homogeneousVectorSpaceBasis : Module.Basis (HomogeneousBasisIndex ℳ) K M :=
  (Decomposition.isInternal ℳ).collectedBasis (fun d => Module.Free.chooseBasis K (ℳ d))

theorem homogeneousVectorSpaceBasis_mem (i : HomogeneousBasisIndex ℳ) :
    homogeneousVectorSpaceBasis ℳ i ∈ ℳ i.1 :=
  (Decomposition.isInternal ℳ).collectedBasis_mem (fun d => Module.Free.chooseBasis K (ℳ d)) i

@[instance_reducible]
def homogeneousBasisIndexFintype [Module.Finite K M] : Fintype (HomogeneousBasisIndex ℳ) :=
  FiniteDimensional.fintypeBasisIndex (homogeneousVectorSpaceBasis ℳ)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousVectorSpaceBasis
