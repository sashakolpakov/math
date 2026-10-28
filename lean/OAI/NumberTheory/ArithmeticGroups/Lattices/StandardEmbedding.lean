import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient
import OAI.NumberTheory.ArithmeticGroups.Lattices.CosetHomeomorphism

/-! # Standard Embedding -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.StandardEmbedding.Construction

noncomputable section

/-! Closed embedding for the exact full archimedean point product and
standard lattice stabilizer appearing in the Lattices arithmetic model. -/

open scoped Classical _root_.NumberField

theorem standardArithmetic_map_pointsEquiv
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    ((G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).map (G.diagonal Set.univ)).map
      (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G).toMonoidHom =
        (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n).subgroupOf (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) := by
  rw [Subgroup.map_map]
  have he : (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G).toMonoidHom.comp (G.diagonal Set.univ) =
      Archimedean.Quotient.Construction.fullArchimedeanRationalPointMap G := by
    apply MonoidHom.ext
    intro g
    exact Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv_diagonal G g
  rw [he, Archimedean.Quotient.Construction.fullArchimedean_standard_arithmetic_subgroup]

def standardArithmeticQuotientHomeomorph
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    (G.ArchimedeanProduct Set.univ ⧸
      (G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).map (G.diagonal Set.univ)) ≃ₜ
    (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G ⧸
      (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n).subgroupOf (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G)) :=
  (CosetHomeomorphism.Construction.cosetHomeomorphOfContinuousMulEquiv (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G)
    ((G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).map (G.diagonal Set.univ))).trans
      (ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq (standardArithmetic_map_pointsEquiv G))

def standardArithmeticQuotientEmbedding
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    (G.ArchimedeanProduct Set.univ ⧸
      (G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).map (G.diagonal Set.univ)) →
    (Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n ⧸ Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n) :=
  ClosedOrbitQuotient.Construction.subgroupCosetMap (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n) ∘
    standardArithmeticQuotientHomeomorph G

theorem standardArithmeticQuotientEmbedding_closed
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    Topology.IsClosedEmbedding (standardArithmeticQuotientEmbedding G) :=
  (Archimedean.Quotient.Construction.fullArchimedeanMatrixGroup_quotient_closedEmbedding G hconn hsemi).comp
    (standardArithmeticQuotientHomeomorph G).isClosedEmbedding

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.StandardEmbedding.Construction
