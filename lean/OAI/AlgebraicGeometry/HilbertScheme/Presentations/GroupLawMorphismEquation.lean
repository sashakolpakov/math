import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroupLawFiniteIdentities

/-! # Group Law Morphism Equation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroupLawMorphismEquation.Core

noncomputable section

/-! An actual natural morphism equation for group-law preservation.
Its source is the product of the given proper flat finitely presented family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

def groupProductTransformation : HomFunctor.Hom.morphismFunctor A A ⟶ HomFunctor.Hom.morphismFunctor (A ⨯ A) A where
  app _T := ↾fun f => GroupLawFiniteIdentities.Core.groupProductValue A f
  naturality _T _U a := by
    ext f
    exact GroupLawFiniteIdentities.Core.groupProductValue_baseChange A f a.unop

def productGroupTransformation : HomFunctor.Hom.morphismFunctor A A ⟶ HomFunctor.Hom.morphismFunctor (A ⨯ A) A where
  app _T := ↾fun f => GroupLawFiniteIdentities.Core.productGroupValues A f
  naturality _T _U a := by
    ext f
    exact GroupLawFiniteIdentities.Core.productGroupValues_baseChange A f a.unop

variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]

def groupLawMorphismEquation : Endomorphisms.Core.FamilyMorphismEquation (HomFunctor.Hom.morphismFunctor A A) where
  source := A ⨯ A
  target := A
  flat := by
    have : Flat (prod.fst : A ⨯ A ⟶ A).left := by
      rw [← Over.prodLeftIsoPullback_hom_fst]
      infer_instance
    rw [← (prod.fst : A ⨯ A ⟶ A).w]
    infer_instance
  proper := by
    have : IsProper (prod.fst : A ⨯ A ⟶ A).left := by
      rw [← Over.prodLeftIsoPullback_hom_fst]
      infer_instance
    rw [← (prod.fst : A ⨯ A ⟶ A).w]
    infer_instance
  finitelyPresented := by
    have : LocallyOfFinitePresentation (prod.fst : A ⨯ A ⟶ A).left := by
      rw [← Over.prodLeftIsoPullback_hom_fst]
      infer_instance
    rw [← (prod.fst : A ⨯ A ⟶ A).w]
    infer_instance
  separated := inferInstance
  lhs := groupProductTransformation A
  rhs := productGroupTransformation A

theorem groupLawMorphismEquation_iff {T : Over S} (f : T ⨯ A ⟶ A) :
    (groupLawMorphismEquation A).lhs.app (.op T) f =
      (groupLawMorphismEquation A).rhs.app (.op T) f ↔ Endomorphisms.Core.PreservesGroupLaw A f :=
  (GroupLawFiniteIdentities.Core.preservesGroupLaw_iff_product_identity A f).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroupLawMorphismEquation.Core
