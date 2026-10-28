import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.RealQuotientEmbedding
import OAI.NumberTheory.ArithmeticGroups.Lattices.StandardEmbedding

/-! # Embedding Representatives -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.EmbeddingRepresentatives.Construction

noncomputable section

section

/-! The standard arithmetic quotient of a connected semisimple number-
field group embeds as a closed subspace of a real lattice quotient. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem standardArithmetic_real_quotient_closedEmbedding
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Module.Basis (Fin m) ℝ (Fin n → mixedSpace k))
    (hb : Submodule.span ℤ (Set.range b) = IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    Topology.IsClosedEmbedding
      (Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding b ∘ StandardEmbedding.Construction.standardArithmeticQuotientEmbedding G) :=
  (Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding_closed b hb).comp
    (StandardEmbedding.Construction.standardArithmeticQuotientEmbedding_closed G hconn hsemi)

theorem exists_standardArithmetic_real_quotient_closedEmbedding
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    ∃ m : ℕ, ∃ b : Module.Basis (Fin m) ℝ (Fin n → mixedSpace k),
      Submodule.span ℤ (Set.range b) = IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module ∧
      Topology.IsClosedEmbedding
        (Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding b ∘ StandardEmbedding.Construction.standardArithmeticQuotientEmbedding G) := by
  let Λ := IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module
  let : DiscreteTopology Λ := IntegralLattice.Construction.vectorLatticeImage_discrete _ (IntegralLattice.FullLattice.standard k n).finite
  let : IsZLattice ℝ Λ := ⟨Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_full k n⟩
  let B := Module.finBasis ℤ Λ
  let b := B.ofZLatticeBasis ℝ
  refine ⟨Module.finrank ℤ Λ, b, B.ofZLatticeBasis_span ℝ, ?_⟩
  exact standardArithmetic_real_quotient_closedEmbedding G hconn hsemi b (B.ofZLatticeBasis_span ℝ)

end

/-! The closed arithmetic embeddings send a coset representative to its
actual real matrix representative. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem standardArithmeticQuotientEmbedding_mk
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.ArchimedeanProduct Set.univ) :
    StandardEmbedding.Construction.standardArithmeticQuotientEmbedding G (QuotientGroup.mk g) =
      QuotientGroup.mk (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G g).val := by
  simp only [StandardEmbedding.Construction.standardArithmeticQuotientEmbedding, Function.comp_apply,
    StandardEmbedding.Construction.standardArithmeticQuotientHomeomorph, Homeomorph.trans_apply,
    CosetHomeomorphism.Construction.cosetHomeomorphOfContinuousMulEquiv_mk, ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq_mk, ClosedOrbitQuotient.Construction.subgroupCosetMap_mk]

theorem minkowskiRealQuotientEmbedding_mk
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (b : Module.Basis (Fin m) ℝ (Fin n → mixedSpace k)) (g : Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n) :
    Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding b (QuotientGroup.mk g) =
      QuotientGroup.mk (RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
        (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b g) := by
  rw [Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding, Function.comp_apply, ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq_mk]
  rfl

theorem standardArithmeticRealEmbedding_mk
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Module.Basis (Fin m) ℝ (Fin n → mixedSpace k))
    (g : G.ArchimedeanProduct Set.univ) :
    (Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding b ∘ StandardEmbedding.Construction.standardArithmeticQuotientEmbedding G) (QuotientGroup.mk g) =
      QuotientGroup.mk (RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
        (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G g).val) := by
  rw [Function.comp_apply, standardArithmeticQuotientEmbedding_mk, minkowskiRealQuotientEmbedding_mk]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.EmbeddingRepresentatives.Construction
