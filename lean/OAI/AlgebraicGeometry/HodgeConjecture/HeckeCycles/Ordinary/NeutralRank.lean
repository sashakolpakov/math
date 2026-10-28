import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionSchemeRank
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRank
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCounts

/-! # Neutral Rank -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.NeutralRank.CM

noncomputable section

/-! The connected factor of the original ordinary q-power torsion scheme
has rank q^(ng), obtained by cancelling the constructed etale factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (q : ℕ) [Fact q.Prime]

theorem neutral_finrank
    (hordinary : Nat.card (A.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) (z : Spec (.of k)) :
    letI : IsFinite (A.torsionScheme (q ^ n)).hom :=
      TorsionFinite.CM.torsion_finite A q hordinary n
    (Finite.GroupDecomposition.CM.neutralPart (@Grp.mk _ _ _ (A.torsionScheme (q ^ n))
      (A.torsionScheme_group (q ^ n)))).X.hom.finrank z = (q ^ n) ^ g := by
  let : IsFinite (A.torsionScheme (q ^ n)).hom :=
    TorsionFinite.CM.torsion_finite A q hordinary n
  let Tor : Grp (Over (Spec (.of k))) := Grp.mk (A.torsionScheme (q ^ n))
  let : IsFinite Tor.X.hom := TorsionFinite.CM.torsion_finite A q hordinary n
  let : IsCommMonObj Tor.X := A.torsionScheme_commutative (q ^ n)
  have hp : Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ Tor.X) = (q ^ n) ^ g := by
    exact (Nat.card_congr (A.torsionSchemePointsEquiv (q ^ n)
      (Over.mk (𝟙 (Spec (.of k)))))).trans
        ((TorsionCounts.CM.ordinary_torsionTower_card
          A.scheme q g hordinary n).trans (pow_mul q n g))
  have h := Finite.GroupRank.CM.connected_times_points Tor z
  rw [hp] at h
  have ht : Tor.X.hom.finrank z = (q ^ n) ^ (2 * g) :=
    TorsionSchemeRank.CM.ordinary_torsion_finrank A q hordinary n z
  have he : (Finite.GroupDecomposition.CM.neutralPart Tor).X.hom.finrank z * (q ^ n) ^ g =
      (q ^ n) ^ g * (q ^ n) ^ g := by
    rw [h, ht, two_mul, pow_add]
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (pow_pos (Fact.out : q.Prime).pos n) g) he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.NeutralRank.CM
