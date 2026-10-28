import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidue

/-! # Point Rational Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointRationalZero

noncomputable section

/-! A field-valued point whose underlying point is a rational section equals that section over its actual base map. This supplies scheme-theoretic zero at residue points without assuming algebraic closure. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem fromSpecResidueField_rational_section
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _) :
    let x := z (IsLocalRing.closedPoint K)
    X.fromSpecResidueField x = (X.fromSpecResidueField x ≫ p) ≫ z := by
  let x := z (IsLocalRing.closedPoint K)
  let r := X.fromSpecResidueField x
  let e := Rational.PointResidue.rationalPointResidueIso p z hz
  let w := Spec.map e.inv
  have hcomp : w ≫ Spec.map e.hom = 𝟙 (Spec (X.residueField x)) :=
    (Spec.map_comp e.hom e.inv).symm.trans
      ((congrArg (fun q => Spec.map q) e.hom_inv_id).trans (Spec.map_id _))
  have hf : w ≫ z = r :=
    (congrArg (fun v => w ≫ v) (Rational.PointResidue.rationalPointResidueIso_factor p z hz).symm).trans
      ((Category.assoc w (Spec.map e.hom) r).symm.trans
        ((congrArg (fun v => v ≫ r) hcomp).trans (Category.id_comp r)))
  have hw : r ≫ p = w :=
    (congrArg (fun v => v ≫ p) hf).symm.trans
      ((Category.assoc w z p).trans
        ((congrArg (fun v => w ≫ v) hz).trans (Category.comp_id w)))
  exact hf.symm.trans (congrArg (fun v => v ≫ z) hw.symm)

theorem fieldPoint_eq_rational_section_of_point
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (t : Spec (.of L) ⟶ X)
    (ht : t (IsLocalRing.closedPoint L) = z (IsLocalRing.closedPoint K)) :
    t = (t ≫ p) ≫ z := by
  let x := t (IsLocalRing.closedPoint L)
  let r := X.fromSpecResidueField x
  let w := Spec.map (X.descResidueField (Scheme.stalkClosedPointTo t))
  have hf : w ≫ r = t := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L X t
  have hr : r = (r ≫ p) ≫ z :=
    (congrArg (fun y : X => X.fromSpecResidueField y = (X.fromSpecResidueField y ≫ p) ≫ z) ht).mpr
      (fromSpecResidueField_rational_section p z hz)
  calc
    t = w ≫ r := hf.symm
    _ = w ≫ ((r ≫ p) ≫ z) := congrArg (fun v => w ≫ v) hr
    _ = ((w ≫ r) ≫ p) ≫ z :=
      ((Category.assoc w (r ≫ p) z).symm.trans
        (congrArg (fun v => v ≫ z) (Category.assoc w r p).symm))
    _ = (t ≫ p) ≫ z := congrArg (fun v => (v ≫ p) ≫ z) hf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointRationalZero
