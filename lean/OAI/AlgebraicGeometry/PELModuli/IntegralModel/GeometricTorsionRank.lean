import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CanonicalDegree
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAbelianDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Geometric Torsion Rank -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricTorsionRank

noncomputable section

/-! The actual geometric torsion scheme has order m^(2g). Its rank is
derived from the proved multiplication degree and the actual kernel square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))

omit [IsAlgClosed K] in
theorem degreeSupport_torsion_finite (m : ℕ) [IsFinite (A.torsionScheme m).hom] :
    IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A.scheme m).hom := by
  let H := ArithmeticGeometry.OrdinaryLocus.Openness.FinitePresentation.Construction.torsion_isPullback A.scheme m
  have h := H.isoPullback_hom_snd
  let p := pullback.snd (A.multiplication m).left η[A.scheme].left
  have hp : IsFinite p := inferInstanceAs (IsFinite (A.torsionScheme m).hom)
  have hi : IsFinite H.isoPullback.hom := inferInstance
  change H.isoPullback.hom ≫ p = (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A.scheme m).hom at h
  exact h ▸ MorphismProperty.IsStableUnderComposition.comp_mem H.isoPullback.hom p hi hp

theorem geometric_torsion_finrank (m : ℕ) (hm : 0 < m) [IsFinite (A.torsionScheme m).hom]
    (z : Spec (.of K)) : (A.torsionScheme m).hom.finrank z = m ^ (2 * g) := by
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A.scheme m).hom := degreeSupport_torsion_finite A m
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.multiplicationMap A.scheme m).left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A.scheme m
  have : IsFinite (A.multiplication m).left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A.scheme m
  have : Flat (A.multiplication m).left :=
    (ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A.scheme m).2
  change (pullback.snd (A.multiplication m).left η[A.scheme].left).finrank z = _
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _
    (IsPullback.of_hasPullback (A.multiplication m).left η[A.scheme].left) z).trans
      (CanonicalDegree.geometric_multiplication_degree A.scheme m hm g (GeometricAbelianDimension.geometric_abelian_dimension A) _)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricTorsionRank
