import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.LawsBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GroupObjectClassifier

/-! # Operation Group Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Equalities of transported operation diagrams give group-preserving
family isomorphisms, including the canonical geometric base-change iso. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {X Y : Over S}

theorem FamilyGroup.Operations.FamilyGroupOperations.ofIso_isMonHom (D : FamilyGroup.Operations.FamilyGroupOperations X)
    (e : X ≅ Y) (hD : D.Laws) :
    letI := D.groupObj hD
    letI := (D.ofIso e).groupObj (D.ofIso_laws e hD)
    IsMonHom e.hom := by
  let : GrpObj X := D.groupObj hD
  exact isMonHom_ofIso e

theorem FamilyGroup.Operations.FamilyGroupOperations.isMonHom_of_operationEq (D : FamilyGroup.Operations.FamilyGroupOperations X)
    (E : FamilyGroup.Operations.FamilyGroupOperations Y) (e : X ≅ Y) (hD : D.Laws) (hE : E.Laws)
    (h : E = D.ofIso e) :
    letI := D.groupObj hD
    letI := E.groupObj hE
    IsMonHom e.hom := by
  subst E
  exact D.ofIso_isMonHom e hD

theorem FamilyGroup.Operations.FamilyGroupOperations.isMonHom_of_ofGrpObj_eq [GrpObj X] [IsCommMonObj X]
    [GrpObj Y] [IsCommMonObj Y] (e : X ≅ Y)
    (h : FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj Y = (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj X).ofIso e) :
    IsMonHom e.hom :=
  (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj X).isMonHom_of_operationEq
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj Y) e (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj_laws X)
      (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj_laws Y) h

variable {U T : Over S} {A : Over S}

theorem FamilyGroup.Operations.FamilyGroupOperations.geometricBaseChangeIso_isMonHom
    (D : FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback T.hom).obj A)) (f : U ⟶ T)
    (E : FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback U.hom).obj A))
    (hD : D.Laws) (hE : E.Laws) (h : E = D.geometricBaseChange f) :
    letI := D.groupObj hD
    letI := E.groupObj hE
    IsMonHom (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).inv := by
  let : GrpObj ((Over.pullback T.hom).obj A) := D.groupObj hD
  exact (D.baseChange f.left).isMonHom_of_operationEq E
    (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).symm (D.baseChange_laws f.left hD) hE h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
