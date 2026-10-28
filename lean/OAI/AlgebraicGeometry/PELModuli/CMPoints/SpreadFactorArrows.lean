import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarFactorPair
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexDiagramSpreading

/-! # Spread Factor Arrows -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadFactorArrows.ScalarFactorDiagram

noncomputable section

/-! Extract the splitting and integral-basis arrows of the spread
factor diagram with their original complex comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {n r g : ℕ} {d : Fin n → ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) Foundations.Scheme.ProjectiveSpace.complexBase)
  (D : TorsionFactorIso.AbelianScalarFactorization A B)
  {O : Type*} [CommRing O] (basis : Module.Basis (Fin r) ℤ O)
  (action : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction O (B i))
  (M : AbelianArithmeticModels.AbelianNumberFieldModel A) (N : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (B i))
  (Q : ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel (ScalarFactorPair.ScalarFactorDiagram.diagram A B D basis action) (ScalarFactorPair.ScalarFactorDiagram.models A B D basis action M N))
  (R : AbelianDiagramSpreading.SpreadFiniteAbelianDiagram Q.diagram Q.embedding)

structure SpreadArrow (p : Fin n × Fin (r + 2)) where
  arrow : (R.abelian (ScalarFactorPair.ScalarFactorDiagram.sourcePair p.1 p.2)).scheme ⟶ (R.abelian (ScalarFactorPair.ScalarFactorDiagram.targetPair p.1 p.2)).scheme
  group : IsMonHom arrow
  compatible : (Over.pullback R.base.complexPoint).map arrow ≫
    (Q.spreadComplexComparison R (ScalarFactorPair.ScalarFactorDiagram.targetPair p.1 p.2)).hom =
      (Q.spreadComplexComparison R (ScalarFactorPair.ScalarFactorDiagram.sourcePair p.1 p.2)).hom ≫ ScalarFactorPair.ScalarFactorDiagram.mapPair A B D basis action p.1 p.2

def spreadArrow (i : Fin n) (k : Fin (r + 2)) : SpreadArrow A B D basis action M N Q R (i, k) := by
  let a := finProdFinEquiv (i, k)
  have h : SpreadArrow A B D basis action M N Q R (finProdFinEquiv.symm a) := {
    arrow := R.map a
    group := R.group a
    compatible := Q.spreadComplexComparison_compatible R a }
  exact (finProdFinEquiv.symm_apply_apply (i, k)) ▸ h

def spreadForward (i : Fin n) : (R.abelian (0 : Fin (n + 1))).scheme ⟶ (R.abelian i.succ).scheme :=
  (spreadArrow A B D basis action M N Q R i 0).arrow

theorem spreadForward_compatible (i : Fin n) :
    (Over.pullback R.base.complexPoint).map (spreadForward A B D basis action M N Q R i) ≫
      (Q.spreadComplexComparison R i.succ).hom =
        (Q.spreadComplexComparison R (0 : Fin (n + 1))).hom ≫ D.forward i :=
  (spreadArrow A B D basis action M N Q R i 0).compatible

def spreadBackward (i : Fin n) : (R.abelian i.succ).scheme ⟶ (R.abelian (0 : Fin (n + 1))).scheme :=
  (spreadArrow A B D basis action M N Q R i (Fin.succ 0)).arrow

theorem spreadBackward_compatible (i : Fin n) :
    (Over.pullback R.base.complexPoint).map (spreadBackward A B D basis action M N Q R i) ≫
      (Q.spreadComplexComparison R (0 : Fin (n + 1))).hom =
        (Q.spreadComplexComparison R i.succ).hom ≫ D.backward i :=
  (spreadArrow A B D basis action M N Q R i (Fin.succ 0)).compatible

def spreadBasisAction (i : Fin n) (j : Fin r) : (R.abelian i.succ).scheme ⟶ (R.abelian i.succ).scheme :=
  (spreadArrow A B D basis action M N Q R i j.succ.succ).arrow

theorem spreadBasisAction_group (i : Fin n) (j : Fin r) :
    IsMonHom (spreadBasisAction A B D basis action M N Q R i j) :=
  (spreadArrow A B D basis action M N Q R i j.succ.succ).group

theorem spreadBasisAction_compatible (i : Fin n) (j : Fin r) :
    (Over.pullback R.base.complexPoint).map (spreadBasisAction A B D basis action M N Q R i j) ≫
      (Q.spreadComplexComparison R i.succ).hom =
        (Q.spreadComplexComparison R i.succ).hom ≫ (action i).map (basis j) :=
  (spreadArrow A B D basis action M N Q R i j.succ.succ).compatible

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadFactorArrows.ScalarFactorDiagram
