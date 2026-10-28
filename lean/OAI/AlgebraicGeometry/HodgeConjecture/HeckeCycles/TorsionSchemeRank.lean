import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryQuotients
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDimension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionFinite

/-! # Torsion Scheme Rank -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionSchemeRank.CM

noncomputable section

/-! The original abelian torsion scheme has its full scheme-theoretic
order, including nilpotents, at every finite ordinary torsion level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

theorem torsion_finrank (m : ℕ) (hm : 0 < m) [IsFinite (A.torsionScheme m).hom]
    (z : Spec (.of k)) : (A.torsionScheme m).hom.finrank z = m ^ (2 * g) := by
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A.scheme m).hom :=
    AbelianScheme.FrobeniusKernel.OrdinaryQuotients.Construction.e40_torsion_finite A m
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.multiplicationMap A.scheme m).left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A.scheme m
  have : IsFinite (A.multiplication m).left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A.scheme m
  have : Flat (ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.multiplicationMap A.scheme m).left :=
    (ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A.scheme m).2
  have : Flat (A.multiplication m).left :=
    (ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A.scheme m).2
  have : Nonempty A.scheme.left := ⟨η[A.scheme].left z⟩
  have : IsOpenImmersion (𝟙 A.scheme : A.scheme ⟶ A.scheme).left :=
    inferInstanceAs (IsOpenImmersion (𝟙 A.scheme.left))
  have hg : topologicalKrullDim A.scheme.left = (g : WithBot ℕ∞) :=
    AbelianScheme.FrobeniusKernel.QuotientDimension.Construction.groupDimension_of_smooth_open A.scheme A.scheme (𝟙 _) g
  change (Limits.pullback.snd (A.multiplication m).left η[A.scheme].left).finrank z = _
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _
    (IsPullback.of_hasPullback (A.multiplication m).left η[A.scheme].left) z).trans
      (ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree.Construction.multiplication_finrank_eq_power_dimension A.scheme m hm g hg _)

theorem ordinary_torsion_finrank (q : ℕ) [Fact q.Prime]
    (hordinary : Nat.card (A.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) (z : Spec (.of k)) :
    (A.torsionScheme (q ^ n)).hom.finrank z = (q ^ n) ^ (2 * g) := by
  let : IsFinite (A.torsionScheme (q ^ n)).hom :=
    Ordinary.TorsionFinite.CM.torsion_finite A q hordinary n
  exact torsion_finrank A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) z

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionSchemeRank.CM
