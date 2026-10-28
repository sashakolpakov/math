import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarAxisGroup
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberSectionIsoTransport

/-! # Scalar Vertical Axis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarVerticalAxis.Construction

noncomputable section

/-! The scalar comparison preserves the original vertical-axis frame
on every test scheme, by pullback from the dual abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

theorem fiberFrame_iso_transport_eq {S : Scheme} {E T T' : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (f : T' ⟶ T)
    (x y : T ⟶ E) (x' y' : T' ⟶ E) (hx : f ≫ x = x') (hy : f ≫ y = y')
    (e : Picard.PoincareBundle.Line.Fibers.fiber L x ≅ Picard.PoincareBundle.Line.Fibers.fiber L y) (e' : Picard.PoincareBundle.Line.Fibers.fiber L x' ≅ Picard.PoincareBundle.Line.Fibers.fiber L y')
    (he : (Scheme.Modules.pullback f.left).mapIso e ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f y y' hy =
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f x x' hx ≪≫ e')
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L x) (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L x')
    (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L y) (v' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L y')
    (hs : Picard.PoincareBundle.Line.Fibers.pullSection L f x x' hx s.hom = s'.hom)
    (hv : Picard.PoincareBundle.Line.Fibers.pullSection L f y y' hy v.hom = v'.hom) (h : s ≪≫ e = v) : s' ≪≫ e' = v' := by
  have hn := FiberSectionIsoTransport.Construction.fiberSection_iso_transport_natural L f x y x' y' hx hy e e' he s.hom s'.hom hs
  exact Iso.ext (hn.symm.trans ((congrArg (fun a => Picard.PoincareBundle.Line.Fibers.pullSection L f y y' hy a)
    (congrArg Iso.hom h)).trans hv))

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (n : ℕ)

theorem poincareScalarVerticalAxis {T : Over (Spec (.of k))} (t : T ⟶ D.abelian.scheme) :
    VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (t ^ n) (1 : T ⟶ A.scheme)) (lift_snd _ _) ≪≫
      ScalarLine.Construction.poincareScalarFiberComparison D n t 1 =
    VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t ((1 : T ⟶ A.scheme) ^ n))
      ((lift_snd _ _).trans (one_pow n)) := by
  let b := (𝟙 D.abelian.scheme)
  let a := (1 : D.abelian.scheme ⟶ A.scheme)
  have hb : t ≫ lift b a = lift t (1 : T ⟶ A.scheme) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [b, a, Category.assoc, lift_fst, lift_snd, Category.comp_id, MonObj.comp_one]
  have hl : t ≫ lift (b ^ n) a = lift (t ^ n) (1 : T ⟶ A.scheme) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [b, a, Category.assoc, lift_fst, lift_snd, MonObj.comp_pow, Category.comp_id, MonObj.comp_one]
  have hr : t ≫ lift b (a ^ n) = lift t ((1 : T ⟶ A.scheme) ^ n) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [b, a, Category.assoc, lift_fst, lift_snd, Category.comp_id, MonObj.comp_pow, MonObj.comp_one]
  exact fiberFrame_iso_transport_eq (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) t _ _ _ _ hl hr
    (ScalarLine.Construction.poincareScalarFiberComparison D n b a) (ScalarLine.Construction.poincareScalarFiberComparison D n t 1)
    (ScalarNaturality.Construction.poincareScalarFiberComparison_pullback D n t b a t 1 hb hl hr)
    (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (b ^ n) a) (lift_snd _ _))
    (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (t ^ n) (1 : T ⟶ A.scheme)) (lift_snd _ _))
    (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift b (a ^ n)) ((lift_snd _ _).trans (one_pow n)))
    (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t ((1 : T ⟶ A.scheme) ^ n)) ((lift_snd _ _).trans (one_pow n)))
    (VerticalUnits.Construction.poincareVerticalUnitFrame_natural D t _ _ (lift_snd _ _) (lift_snd _ _) hl)
    (VerticalUnits.Construction.poincareVerticalUnitFrame_natural D t _ _
    ((lift_snd _ _).trans (one_pow n)) ((lift_snd _ _).trans (one_pow n)) hr)
    (ScalarAxisGroup.Construction.poincareScalarVerticalAxis_group D b n)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarVerticalAxis.Construction
