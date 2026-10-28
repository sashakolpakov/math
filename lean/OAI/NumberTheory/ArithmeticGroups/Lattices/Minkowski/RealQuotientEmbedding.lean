import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.RealClosedImage
import OAI.NumberTheory.ArithmeticGroups.Lattices.HomCosetEmbedding
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.FrameTopology

/-! # Real Quotient Embedding -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.RealQuotientEmbedding.Construction

noncomputable section

/-! The actual full archimedean arithmetic quotient embeds as a closed
subspace of a real special-linear lattice quotient. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem minkowski_real_arithmetic_comap
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (b : Module.Basis (Fin m) ℝ (Fin n → mixedSpace k)) :
    ((SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b)
      (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module)).comap Matrix.SpecialLinearGroup.toGL).comap
        (RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
          (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b) = Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n := by
  ext g
  change (RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
      (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b g).toGL ∈
    SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b)
      (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) ↔ g ∈ Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n
  rw [Stabilizer.Construction.fullArchimedeanIntegralSL_eq_minkowski_stabilizer]
  simp only [StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff]
  change (∀ x, LatticeFrameAction.Construction.matrixFrameAction b (RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
      (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b g).toGL x ∈
      IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module ↔
        x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) ↔
    ∀ x, Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module ↔
      x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module
  rw [RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates_frame_action]

def minkowskiRealQuotientEmbedding
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (b : Module.Basis (Fin m) ℝ (Fin n → mixedSpace k)) :
    (Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n ⧸ Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n) →
    (Algebraic.SL m ℝ ⧸ (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b)
      (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module)).comap Matrix.SpecialLinearGroup.toGL) :=
  HomCosetEmbedding.Construction.homSubgroupCosetMap (RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
      (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b) _ ∘
    ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq (minkowski_real_arithmetic_comap b).symm

theorem minkowskiRealQuotientEmbedding_closed
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (b : Module.Basis (Fin m) ℝ (Fin n → mixedSpace k))
    (hb : Submodule.span ℤ (Set.range b) = IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    Topology.IsClosedEmbedding (minkowskiRealQuotientEmbedding b) := by
  let Λ := IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module
  let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ).comap Matrix.SpecialLinearGroup.toGL
  let f := RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
    (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b
  let : DiscreteTopology Λ := IntegralLattice.Construction.vectorLatticeImage_discrete _ (IntegralLattice.FullLattice.standard k n).finite
  let : DiscreteTopology Γ := Integral.FrameTopology.Construction.special_frame_stabilizer_discrete_of_integral_frame Λ b (fun i => by
    change b i ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module
    rw [← hb]
    exact Submodule.subset_span (Set.mem_range_self i))
  let : LocallyCompactSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → ℝ))
  let : LocallyCompactSpace (Algebraic.SL m ℝ) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  have hf : Continuous f := RealSpecialLinearCoordinates.Construction.continuous_realSpecialLinearCoordinates _ _ b
    (Archimedean.Quotient.Construction.continuous_archimedeanRealRepresentation_apply k n)
  have hclosed : IsClosed ((QuotientGroup.mk : Algebraic.SL m ℝ → Algebraic.SL m ℝ ⧸ Γ) '' Set.range f) :=
    RealClosedImage.Construction.minkowski_real_quotient_image_closed b hb
  exact (HomCosetEmbedding.Construction.homSubgroupCosetMap_closedEmbedding f hf Γ hclosed).comp
    (ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq (minkowski_real_arithmetic_comap b).symm).isClosedEmbedding

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.RealQuotientEmbedding.Construction
