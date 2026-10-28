import OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadFactorArrows
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericIntegralAction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ActionTransport

/-! # Spread Actions -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadActions.ScalarFactorDiagram

noncomputable section

/-! Recover the full relative integer action from the spread basis
endomorphisms, preserving its specified complex CM comparison. -/

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

def spreadComplexAction (i : Fin n) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction O ((R.abelian i.succ).pullback R.base.complexPoint) := by
  let e : ((R.abelian i.succ).pullback R.base.complexPoint).scheme ≅ (B i).scheme :=
    Q.spreadComplexComparison R i.succ
  let : IsMonHom e.hom := Q.spreadComplexComparison_group R i.succ
  exact @ActionTransport.integralActionOfIso _ _ _ _ _ e.symm (inferInstanceAs (IsMonHom e.inv)) _ _ (action i)

theorem spreadBasisAction_pullback (i : Fin n) (j : Fin r) :
    (Over.pullback R.base.complexPoint).map (SpreadFactorArrows.ScalarFactorDiagram.spreadBasisAction A B D basis action M N Q R i j) =
      (spreadComplexAction A B D basis action M N Q R i).map (basis j) :=
  (((Q.spreadComplexComparison R i.succ).eq_comp_inv).mpr
    (SpreadFactorArrows.ScalarFactorDiagram.spreadBasisAction_compatible A B D basis action M N Q R i j)).trans (Category.assoc _ _ _)

def spreadFullAction (i : Fin n) : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O (R.abelian i.succ) := by
  let : IsDomain R.base.R := Function.Injective.isDomain R.base.toField R.base.toField_injective
  let : IsReduced R.base.base := inferInstanceAs (IsReduced (Spec (.of R.base.R)))
  let : IsLocallyNoetherian R.base.base := inferInstanceAs (IsLocallyNoetherian (Spec (.of R.base.R)))
  let : IsDominant R.base.complexPoint := R.base.complexPoint_dominant
  exact GenericIntegralAction.genericBasisActionLift R.base.complexPoint (R.abelian i.succ) basis
    (spreadComplexAction A B D basis action M N Q R i)
    (SpreadFactorArrows.ScalarFactorDiagram.spreadBasisAction A B D basis action M N Q R i)
    (SpreadFactorArrows.ScalarFactorDiagram.spreadBasisAction_group A B D basis action M N Q R i)
    (spreadBasisAction_pullback A B D basis action M N Q R i)

theorem spreadFullAction_comparison (i : Fin n) :
    (spreadFullAction A B D basis action M N Q R i).pullback R.base.complexPoint =
      spreadComplexAction A B D basis action M N Q R i := by
  let : IsDomain R.base.R := Function.Injective.isDomain R.base.toField R.base.toField_injective
  let : IsReduced R.base.base := inferInstanceAs (IsReduced (Spec (.of R.base.R)))
  let : IsLocallyNoetherian R.base.base := inferInstanceAs (IsLocallyNoetherian (Spec (.of R.base.R)))
  let : IsDominant R.base.complexPoint := R.base.complexPoint_dominant
  exact GenericIntegralAction.genericBasisActionLift_comparison R.base.complexPoint (R.abelian i.succ) basis
    (spreadComplexAction A B D basis action M N Q R i)
    (SpreadFactorArrows.ScalarFactorDiagram.spreadBasisAction A B D basis action M N Q R i)
    (SpreadFactorArrows.ScalarFactorDiagram.spreadBasisAction_group A B D basis action M N Q R i)
    (spreadBasisAction_pullback A B D basis action M N Q R i)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadActions.ScalarFactorDiagram
