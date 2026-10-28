import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericPointCount
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Closed Geometric Point -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedGeometricPoint.Construction

noncomputable section

/-! At a closed point over an algebraically closed field, geometric points
and rational points give the same fiber count. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def geometricPointClosedIso
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed {x}) :
    DefinitionsTorsion.geometricPoint X x ≅ Over.mk (pointOfClosedPoint f x hx) := by
  let e := residueFieldIsoBase f x hx
  have : IsAlgClosed (X.residueField x) :=
    IsAlgClosed.of_ringEquiv K (X.residueField x) e.commRingCatIsoToRingEquiv.symm
  let j : X.residueField x ⟶ .of (AlgebraicClosure (X.residueField x)) :=
    CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))
  have : IsIso j := (ConcreteCategory.isIso_iff_bijective j).mpr
    (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := X.residueField x) (K := AlgebraicClosure (X.residueField x)))
  let α := Scheme.Spec.mapIso (asIso j).op ≪≫ (Scheme.Spec.mapIso e.op).symm
  refine Over.isoMk α ?_
  change (Spec.map j ≫ Spec.map e.inv) ≫
    (Spec.map e.hom ≫ X.fromSpecResidueField x) =
      Spec.map j ≫ X.fromSpecResidueField x
  rw [Category.assoc, ← Category.assoc (Spec.map e.inv), ← Spec.map_comp,
    e.hom_inv_id, Spec.map_id, Category.id_comp]

theorem geometricPointCard_closed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (T : Over X) (x : X) (hx : IsClosed {x}) :
    Nat.card (DefinitionsTorsion.geometricPoint X x ⟶ T) =
      Nat.card (Over.mk (pointOfClosedPoint f x hx) ⟶ T) :=
  Nat.card_congr (Iso.homCongr (geometricPointClosedIso f x hx) (Iso.refl T))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedGeometricPoint.Construction
