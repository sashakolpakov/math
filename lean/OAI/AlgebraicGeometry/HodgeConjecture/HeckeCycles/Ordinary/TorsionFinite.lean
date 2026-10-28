import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCounts
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Torsion Finite -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionFinite.CM

noncomputable section

/-! Every ordinary geometric torsion level is a finite scheme. This
uses its proved point count together with properness of the original
torsion scheme, without a group-scheme splitting assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (q : ℕ) [Fact q.Prime]

theorem torsion_finite
    (hordinary : Nat.card (A.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) : IsFinite (A.torsionScheme (q ^ n)).hom := by
  let hfinite : Finite (A.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) :=
    Nat.finite_of_card_ne_zero (hordinary ▸ pow_ne_zero g (Fact.out : q.Prime).ne_zero)
  have hdiv := @Picard.Homomorphisms.OrdinaryDivision.Construction.rational_points_divisible_of_finite_torsion
    k _ _ A.scheme A.group A.commutative
    (@SmoothOfRelativeDimension.smooth g _ _ _ A.smoothDimension) A.proper A.connected q hfinite
  have hc := TorsionCounts.CM.torsionTower_card q g hordinary
    (fun m => TorsionCounts.CM.OrdinaryDivision.torsionTower_surjective_of_division q m hdiv) n
  let : Finite (A.torsionPoints (q ^ n) (Over.mk (𝟙 (Spec (.of k))))) :=
    Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero (n * g) (Fact.out : q.Prime).ne_zero)
  let : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ A.torsionScheme (q ^ n)) :=
    Finite.of_equiv _ (A.torsionSchemePointsEquiv (q ^ n) (Over.mk (𝟙 (Spec (.of k))))).symm
  exact Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_morphism_of_proper_finite_rationalPoints (A.torsionScheme (q ^ n))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionFinite.CM
