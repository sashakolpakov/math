import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.Single
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! # Homotopy Opposite Unop -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop.HomotopyOpposite

noncomputable section

/-!
# Reading a homotopy equivalence from the opposite category

This lets the simplicial Čech contraction in the opposite coefficient
category act on the corresponding cochain complex of coefficients.
-/

open _root_.CategoryTheory Opposite Simplicial

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]
  {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex Vᵒᵖ c}

def unop (e : HomotopyEquiv K L) : HomotopyEquiv K.unop L.unop where
  hom := (HomologicalComplex.unopFunctor V c).map e.inv.op
  inv := (HomologicalComplex.unopFunctor V c).map e.hom.op
  homotopyHomInvId := e.homotopyHomInvId.unop
  homotopyInvHomId := e.homotopyInvHomId.unop

open _root_.AlgebraicTopology Limits

def cofaceIso (Y : CosimplicialObject V) :
    (AlternatingFaceMapComplex.obj ((cosimplicialSimplicialEquiv V).functor.obj (op Y))).unop ≅
      AlternatingCofaceMapComplex.obj Y :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    change n + 1 = m at hnm
    subst m
    have h0 : (AlternatingCofaceMapComplex.obj Y).d n (n + 1) =
        AlternatingCofaceMapComplex.objD Y n :=
      CochainComplex.of_d (fun i => Y.obj ⦋i⦌) (AlternatingCofaceMapComplex.objD Y) n
    have h1 : (AlternatingFaceMapComplex.obj ((cosimplicialSimplicialEquiv V).functor.obj (op Y))).d
        (n + 1) n = AlternatingFaceMapComplex.objD ((cosimplicialSimplicialEquiv V).functor.obj (op Y)) n :=
      ChainComplex.of_d (fun i => ((cosimplicialSimplicialEquiv V).functor.obj (op Y)).obj (op ⦋i⦌))
        (AlternatingFaceMapComplex.objD ((cosimplicialSimplicialEquiv V).functor.obj (op Y))) n
    exact (Category.id_comp _).trans ((h0.trans ((AlternatingCofaceMapComplex.d_eq_unop_d Y n).trans
      (congrArg Quiver.Hom.unop h1).symm)).trans (Category.comp_id _).symm))

variable [HasZeroObject V]

def singleIso (A : V) : ((ChainComplex.single₀ Vᵒᵖ).obj (op A)).unop ≅
    (CochainComplex.single₀ V).obj A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => by
    by_cases hn : n = 0
    · subst n
      exact Iso.refl _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (op A) n hn).unop.iso
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 A n hn))
    (by
      intro n m _
      change _ ≫ 0 = (0 : ((ChainComplex.single₀ Vᵒᵖ).obj (op A)).X m ⟶
        ((ChainComplex.single₀ Vᵒᵖ).obj (op A)).X n).unop ≫ _
      exact comp_zero.trans zero_comp.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop.HomotopyOpposite
