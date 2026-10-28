import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualBaseChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BaseChange.Construction

noncomputable section

/-! Arbitrary base change of an actual represented Picard image.
The map uses the native homogeneous Picard base-change comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S S' : Scheme.{u}} {B Q : Over S} [GrpObj B] [GrpObj Q]
  (i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj) (s : S' ⟶ S)

def picardImageBaseChangePointMap :
    uliftYoneda.{u + 1}.obj (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup Q s) ⟶
      (Over.map s).op ⋙ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj where
  app T := TypeCat.ofHom (fun x => i.app (op ((Over.map s).obj T.unop))
    (ULift.up (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv Q s T.unop x.down)))
  naturality {T U} a := by
    apply ConcreteCategory.ext_apply
    intro x
    change i.app (op ((Over.map s).obj U.unop))
      (ULift.up (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv Q s U.unop (a.unop ≫ x.down))) = _
    rw [Picard.Homomorphisms.UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangePointsEquiv_precomp]
    exact congrArg (fun b : (uliftYoneda.{u + 1}.obj Q).obj (op ((Over.map s).obj T.unop)) ⟶
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op ((Over.map s).obj U.unop)) =>
        b (ULift.up (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv Q s T.unop x.down)))
      (i.naturality ((Over.map s).map a.unop).op)

def picardImageBaseChangeMap : uliftYoneda.{u + 1}.obj (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup Q s) ⟶
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup B s)).obj :=
  picardImageBaseChangePointMap i s ≫ (Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardSheafBaseChangeIso B s).inv.hom

set_option backward.isDefEq.respectTransparency false in
theorem picardImageBaseChangeMap_value (T : Over S') (x : T ⟶ Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup Q s) :
    Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv B s T
      ((picardImageBaseChangeMap i s).app (op T) (ULift.up x)) =
        i.app (op ((Over.map s).obj T)) (ULift.up (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv Q s T x)) := by
  exact (Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv B s T).apply_symm_apply _

theorem picardImageBaseChangeMap_mono [Mono i] : Mono (picardImageBaseChangeMap i s) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  apply ConcreteCategory.mono_of_injective
  intro x y h
  have he := (picardImageBaseChangeMap_value i s T.unop x.down).symm.trans
    ((congrArg (Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv B s T.unop) h).trans
      (picardImageBaseChangeMap_value i s T.unop y.down))
  have hinj : Function.Injective (i.app (op ((Over.map s).obj T.unop))) :=
    (CategoryTheory.mono_iff_injective _).mp inferInstance
  apply ULift.ext
  exact (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv Q s T.unop).injective (ULift.up_injective (hinj he))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BaseChange.Construction
