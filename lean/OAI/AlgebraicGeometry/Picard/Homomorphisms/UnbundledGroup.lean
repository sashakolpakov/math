import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneous
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupFunctor

/-! # Unbundled Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup

noncomputable section

/-! Tensor product and dualization give the dimension-independent
homogeneous Picard sheaf its intrinsic commutative group structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

theorem homogeneousPicardClass_mul {T : Over S}
    {q r : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T)}
    (hq : (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T q) (hr : (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T r) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T (q * r) := by
  intro U f a
  let H := (RelativeGroup.Construction.toRelativePicardHom A U).comp
    ((SchemePullback.Construction.schemePicardPullback ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left).comp
      (SchemePullback.Construction.schemePicardPullback ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map f)))
  let K := (RelativeGroup.Construction.toRelativePicardHom A U).comp
    (SchemePullback.Construction.schemePicardPullback ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map f))
  change H (q * r) = K (q * r)
  exact (H.map_mul q r).trans
    ((congrArg₂ (fun x y : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A U => x * y) (hq U f a) (hr U f a)).trans
      (K.map_mul q r).symm)

theorem homogeneousPicardClass_inv {T : Over S}
    {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T)}
    (hq : (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T q) : (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T q⁻¹ := by
  intro U f a
  let H := (RelativeGroup.Construction.toRelativePicardHom A U).comp
    ((SchemePullback.Construction.schemePicardPullback ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left).comp
      (SchemePullback.Construction.schemePicardPullback ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map f)))
  let K := (RelativeGroup.Construction.toRelativePicardHom A U).comp
    (SchemePullback.Construction.schemePicardPullback ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map f))
  change H q⁻¹ = K q⁻¹
  rw [H.map_inv, K.map_inv]
  exact congrArg Inv.inv (hq U f a)

def homogeneousPicardSubgroup (T : Over S) :
    Subgroup (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).obj T)) where
  carrier := (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T
  one_mem' := (UnbundledHomogeneous.Construction.UnbundledPicard.trivialClass_homogeneous A) T
  mul_mem' := homogeneousPicardClass_mul A
  inv_mem' := homogeneousPicardClass_inv A

instance homogeneousPicardClassCommGroup (T : (Over S)ᵒᵖ) :
    CommGroup ((UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj T) :=
  inferInstanceAs (CommGroup (homogeneousPicardSubgroup A T.unop))

def homogeneousPicardGroupPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of ((UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj T)
  map f := CommGrpCat.ofHom
    { toFun := (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map f
      map_one' := Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map f.unop))
      map_mul' q r := Subtype.ext (SchemePullback.Construction.pullbackClass_mul ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map f.unop) q.val r.val) }
  map_id T := by
    ext q
    exact (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map_id_apply T q
  map_comp f h := by
    ext q
    exact (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map_comp_apply f h q

def homogeneousPicardGroupInclusion : homogeneousPicardGroupPresheaf A ⟶
    RelativeGroup.Construction.relativePicardGroupPresheaf A where
  app T := CommGrpCat.ofHom (homogeneousPicardSubgroup A T.unop).subtype
  naturality {T U} f := by ext q; rfl

instance homogeneousPicardSectionsCommGroup (T : (Over S)ᵒᵖ) :
    CommGroup ((UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj T) :=
  GroupSheafification.Construction.picardTypeSheafifyCommGroup (homogeneousPicardGroupPresheaf A) T

def homogeneousPicardSheafInclusionHom (T : Over S) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (op T) →* AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A T :=
  GroupSheafMaps.Construction.picardTypeSheafifyMapHom (homogeneousPicardGroupInclusion A) (op T)

theorem homogeneousPicardSheafInclusionHom_apply (T : Over S)
    (q : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (op T)) :
    homogeneousPicardSheafInclusionHom A T q = (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T) q :=
  GroupSheafMaps.Construction.picardTypeSheafifyMapHom_apply (homogeneousPicardGroupInclusion A) (op T) q

theorem trivialHomogeneousPicardClass_eq_one (T : Over S) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A) T = 1 :=
  (GroupSheafification.Construction.picardTypeSheafifyUnitHom (homogeneousPicardGroupPresheaf A) (op T)).map_one

def homogeneousPicardGroupFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  GroupFunctor.Construction.picardTypeGroupSheafFunctor (homogeneousPicardGroupPresheaf A)

def homogeneousPicardGroupForgetIso :
    homogeneousPicardGroupFunctor A ⋙ forget CommGrpCat ≅ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj :=
  GroupFunctor.Construction.picardTypeGroupForgetIso (homogeneousPicardGroupPresheaf A)

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup
