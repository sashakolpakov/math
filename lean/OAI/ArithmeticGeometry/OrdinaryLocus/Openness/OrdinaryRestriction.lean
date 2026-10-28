import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenBaseChange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension

/-! # Ordinary Restriction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrdinaryRestriction.Construction

noncomputable section

/-! Compatibility of the exact Openness ordinary predicate with open restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem topologicalKrullDim_eq_of_isPullback_of_isIso
    {P X Y Z : Scheme} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hp : IsPullback fst snd f g) [IsIso g] :
    topologicalKrullDim P = topologicalKrullDim X := by
  have : IsIso fst := hp.isIso_fst_of_isIso
  exact fst.homeomorph.isHomeomorph.topologicalKrullDim_eq

/-- Restricting the base to an open subscheme preserves each scheme-theoretic fiber. -/
theorem topologicalKrullDim_fiber_openBaseChange
    {S T : Scheme} (i : T ⟶ S) [IsOpenImmersion i] (A : Over S) (t : T) :
    topologicalKrullDim (((Over.pullback i).obj A).hom.fiber t) =
      topologicalKrullDim (A.hom.fiber (i t)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback A.hom i) t
  exact topologicalKrullDim_eq_of_isPullback_of_isIso hp

/-- The ordinary predicate is unchanged by restricting the base to an open subscheme. -/
theorem isOrdinaryAt_openBaseChange_iff
    {S T : Scheme} (i : T ⟶ S) [IsOpenImmersion i] (A : Over S) [GrpObj A]
    (p : ℕ) (t : T) :
    DefinitionsTorsion.IsOrdinaryAt p ((Over.pullback i).obj A) t ↔
      DefinitionsTorsion.IsOrdinaryAt p A (i t) := by
  simp only [DefinitionsTorsion.IsOrdinaryAt, topologicalKrullDim_fiber_openBaseChange,
    OpenBaseChange.Construction.torsionPointCard_openBaseChange]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrdinaryRestriction.Construction
