import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.NeutralRank
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PolarizedCartierRepresentative
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConnectedMultiplicativeCriterion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCharacters

/-! # Multiplicative Factor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.MultiplicativeFactor.CM

noncomputable section

/-! The connected factor of actual ordinary polarized abelian torsion
is the standard multiplicative group at every finite level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (q : ℕ) [Fact q.Prime] [CharP k q]

theorem multiplicative_factor
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) :
    letI : IsFinite (A.abelian.torsionScheme (q ^ n)).hom :=
      TorsionFinite.CM.torsion_finite A.abelian q hordinary n
    Nonempty (Finite.GroupDecomposition.CM.neutralPart (@Grp.mk _ _ _ (A.abelian.torsionScheme (q ^ n))
      (A.abelian.torsionScheme_group (q ^ n))) ≅ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n g) := by
  let : IsFinite (A.abelian.torsionScheme (q ^ n)).hom :=
    TorsionFinite.CM.torsion_finite A.abelian q hordinary n
  let Tor : Grp (Over (Spec (.of k))) := Grp.mk (A.abelian.torsionScheme (q ^ n))
  let : IsFinite Tor.X.hom :=
    TorsionFinite.CM.torsion_finite A.abelian q hordinary n
  let : IsCommMonObj Tor.X := A.abelian.torsionScheme_commutative (q ^ n)
  obtain ⟨e⟩ := PolarizedCartierRepresentative.CM.character_coordinates_all A q hordinary n
  exact ConnectedMultiplicativeCriterion.CM.multiplicative_factor Tor q n g
    (TorsionCharacters.CM.points_killed A.abelian (q ^ n) (Over.mk (𝟙 (Spec (.of k))))) e
    (IsLocalRing.closedPoint k)
    (NeutralRank.CM.neutral_finrank A.abelian q hordinary n (IsLocalRing.closedPoint k))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.MultiplicativeFactor.CM
