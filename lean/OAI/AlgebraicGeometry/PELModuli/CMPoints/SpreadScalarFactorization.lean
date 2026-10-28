import OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadFactorArrows
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarFactorTransport

/-! # Spread Scalar Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadScalarFactorization.ScalarFactorDiagram

noncomputable section

/-! The actual spread splitting arrows satisfy the scalar identities
on the arithmetic models by dominant-fiber faithfulness. -/

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

def spreadComplexSplitting :
    TorsionFactorIso.AbelianScalarFactorization ((R.abelian (0 : Fin (n + 1))).pullback R.base.complexPoint)
      (fun i : Fin n => (R.abelian i.succ).pullback R.base.complexPoint) := by
  let e : ((R.abelian (0 : Fin (n + 1))).pullback R.base.complexPoint).scheme ≅ A.scheme :=
    Q.spreadComplexComparison R (0 : Fin (n + 1))
  let f (i : Fin n) : ((R.abelian i.succ).pullback R.base.complexPoint).scheme ≅ (B i).scheme :=
    Q.spreadComplexComparison R i.succ
  let : IsMonHom e.hom := Q.spreadComplexComparison_group R (0 : Fin (n + 1))
  let (i : Fin n) : IsMonHom (f i).hom := Q.spreadComplexComparison_group R i.succ
  exact D.transport ((R.abelian (0 : Fin (n + 1))).pullback R.base.complexPoint)
    (fun i : Fin n => (R.abelian i.succ).pullback R.base.complexPoint)
    e.symm (fun i => (f i).symm) (inferInstanceAs (IsMonHom e.inv))
    (fun i => inferInstanceAs (IsMonHom (f i).inv))

theorem spreadForward_pullback (i : Fin n) :
    (Over.pullback R.base.complexPoint).map (SpreadFactorArrows.ScalarFactorDiagram.spreadForward A B D basis action M N Q R i) =
      (spreadComplexSplitting A B D basis action M N Q R).forward i :=
  (((Q.spreadComplexComparison R i.succ).eq_comp_inv).mpr
    (SpreadFactorArrows.ScalarFactorDiagram.spreadForward_compatible A B D basis action M N Q R i)).trans (Category.assoc _ _ _)

theorem spreadBackward_pullback (i : Fin n) :
    (Over.pullback R.base.complexPoint).map (SpreadFactorArrows.ScalarFactorDiagram.spreadBackward A B D basis action M N Q R i) =
      (spreadComplexSplitting A B D basis action M N Q R).backward i :=
  (((Q.spreadComplexComparison R (0 : Fin (n + 1))).eq_comp_inv).mpr
    (SpreadFactorArrows.ScalarFactorDiagram.spreadBackward_compatible A B D basis action M N Q R i)).trans (Category.assoc _ _ _)

def spreadRelativeSplitting : TorsionFactorIso.AbelianScalarFactorization (R.abelian (0 : Fin (n + 1)))
    (fun i : Fin n => R.abelian i.succ) := by
  let : IsDomain R.base.R := Function.Injective.isDomain R.base.toField R.base.toField_injective
  let : IsReduced R.base.base := inferInstanceAs (IsReduced (Spec (.of R.base.R)))
  let : IsLocallyNoetherian R.base.base := inferInstanceAs (IsLocallyNoetherian (Spec (.of R.base.R)))
  let : IsDominant R.base.complexPoint := R.base.complexPoint_dominant
  exact ScalarFactorBaseChange.abelianScalarFactorizationOfDominant R.base.complexPoint
    (R.abelian (0 : Fin (n + 1))) (fun i : Fin n => R.abelian i.succ)
    (spreadComplexSplitting A B D basis action M N Q R)
    (SpreadFactorArrows.ScalarFactorDiagram.spreadForward A B D basis action M N Q R) (SpreadFactorArrows.ScalarFactorDiagram.spreadBackward A B D basis action M N Q R)
    (spreadForward_pullback A B D basis action M N Q R)
    (spreadBackward_pullback A B D basis action M N Q R)

theorem spreadRelativeSplitting_multiplier :
    (spreadRelativeSplitting A B D basis action M N Q R).multiplier = D.multiplier := rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadScalarFactorization.ScalarFactorDiagram
