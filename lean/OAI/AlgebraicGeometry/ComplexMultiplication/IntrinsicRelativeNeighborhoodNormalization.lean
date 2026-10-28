import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeNeighborhoodPullback
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Intrinsic Relative Neighborhood Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicRelativeNeighborhoodNormalization

noncomputable section

/-! # Actual native restriction agrees with the actual original neighborhood pair inclusion -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicTopology.Singular

variable (R : Type) [CommRing R] (Y : TopCat.{0}) (S : Set Y) (U : Opens Y) (n : ℕ)

theorem nativeRelativeNeighborhood_normalization
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) Y Sᶜ n) :
    RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv R (TopCat.of U)
      (Subtype.val ⁻¹' S)ᶜ n
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of R R) Y Sᶜ U n a) =
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap R n (RelativeNeighborhoodPullback.neighborhoodToSubsetPair (U : Set Y) S)
      (RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv R Y Sᶜ n a) := by
  exact RelativeDualAbsoluteExtension.relativeSingularCohomologyBridgeEquiv_naturality R
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (fun _ h => h) n a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicRelativeNeighborhoodNormalization
