import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroupLawMorphismEquation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FamilyEquationOperations

/-! # Endomorphism Tuple Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismTupleEquations.Core

noncomputable section

/-! Endomorphism tuples are exactly the solutions of a finite list of
actual group-multiplication equations, naturally on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A]
variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]
variable (n : ℕ)

def endomorphismTupleEquations : List (Endomorphisms.Core.FamilyMorphismEquation (Has.Core.morphismTuples A A n)) :=
  List.ofFn (fun i : Fin n => (GroupLawMorphismEquation.Core.groupLawMorphismEquation A).comap
    (FamilyEquationOperations.Core.tupleProjection (HomFunctor.Hom.morphismFunctor A A) n i))

theorem satisfies_endomorphismTupleEquations_iff {T : Over S}
    (f : (Has.Core.morphismTuples A A n).obj (.op T)) :
    Endomorphisms.Core.SatisfiesEquations (endomorphismTupleEquations A n) f ↔ ∀ i, Endomorphisms.Core.PreservesGroupLaw A (f i) := by
  constructor
  · intro h i
    apply (GroupLawMorphismEquation.Core.groupLawMorphismEquation_iff A (f i)).mp
    exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact (GroupLawMorphismEquation.Core.groupLawMorphismEquation_iff A (f i)).mpr (h i)

def endomorphismTupleSolutions : Endomorphisms.Core.endomorphismTuples A n ⟶
    (Endomorphisms.Core.solutionSubfunctor (endomorphismTupleEquations A n)).toFunctor where
  app T := ↾fun f => ⟨(Endomorphisms.Core.forgetGroupLaw A n).app T f,
    (satisfies_endomorphismTupleEquations_iff A n _).mpr (fun i => (f i).property)⟩
  naturality _T _U _a := by
    ext f
    rfl

def endomorphismTupleEquationEquivalence : Endomorphisms.Core.endomorphismTuples A n ≅
    (Endomorphisms.Core.solutionSubfunctor (endomorphismTupleEquations A n)).toFunctor := by
  have : IsIso (endomorphismTupleSolutions A n) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro T
    apply (isIso_iff_bijective _).mpr
    constructor
    · intro f g h
      funext i
      apply Subtype.ext
      exact congrFun (congrArg Subtype.val h) i
    · intro f
      have hf := (satisfies_endomorphismTupleEquations_iff A n f.val).mp f.property
      exact ⟨fun i => ⟨f.val i, hf i⟩, rfl⟩
  exact asIso (endomorphismTupleSolutions A n)

theorem endomorphismTupleEquationEquivalence_inclusion :
    (endomorphismTupleEquationEquivalence A n).hom ≫
      (Endomorphisms.Core.solutionSubfunctor (endomorphismTupleEquations A n)).ι = Endomorphisms.Core.forgetGroupLaw A n := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismTupleEquations.Core
