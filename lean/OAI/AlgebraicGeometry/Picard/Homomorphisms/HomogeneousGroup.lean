import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection

/-! # Homogeneous Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousGroup

noncomputable section

/-! Homogeneous line-bundle classes form an intrinsic subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {g : ℕ} {S : Scheme.{u}} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem homogeneousPicardClass_mul {T : Over S}
    {q r : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (op T)}
    (hq : A.IsHomogeneousPicardClass T q) (hr : A.IsHomogeneousPicardClass T r) :
    A.IsHomogeneousPicardClass T (q * r) := by
  intro U f a
  let H := (RelativeGroup.Construction.toRelativePicardHom A.scheme U).comp
    ((SchemePullback.Construction.schemePicardPullback (A.translation a).left).comp
      (SchemePullback.Construction.schemePicardPullback ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map f)))
  let K := (RelativeGroup.Construction.toRelativePicardHom A.scheme U).comp
    (SchemePullback.Construction.schemePicardPullback ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map f))
  change H (q * r) = K (q * r)
  exact (H.map_mul q r).trans
    ((congrArg₂ (fun x y : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme U => x * y) (hq U f a) (hr U f a)).trans
      (K.map_mul q r).symm)

theorem homogeneousPicardClass_inv {T : Over S}
    {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (op T)}
    (hq : A.IsHomogeneousPicardClass T q) : A.IsHomogeneousPicardClass T q⁻¹ := by
  intro U f a
  let H := (RelativeGroup.Construction.toRelativePicardHom A.scheme U).comp
    ((SchemePullback.Construction.schemePicardPullback (A.translation a).left).comp
      (SchemePullback.Construction.schemePicardPullback ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map f)))
  let K := (RelativeGroup.Construction.toRelativePicardHom A.scheme U).comp
    (SchemePullback.Construction.schemePicardPullback ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map f))
  change H q⁻¹ = K q⁻¹
  rw [H.map_inv, K.map_inv]
  exact congrArg Inv.inv (hq U f a)

def homogeneousPicardSubgroup (T : Over S) :
    Subgroup (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T)) where
  carrier := A.IsHomogeneousPicardClass T
  one_mem' := A.trivialClass_homogeneous T
  mul_mem' := homogeneousPicardClass_mul A
  inv_mem' := homogeneousPicardClass_inv A

instance homogeneousPicardClassCommGroup (T : (Over S)ᵒᵖ) :
    CommGroup (A.homogeneousPicardPresheaf.obj T) :=
  inferInstanceAs (CommGroup (homogeneousPicardSubgroup A T.unop))

def homogeneousPicardGroupPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (A.homogeneousPicardPresheaf.obj T)
  map f := CommGrpCat.ofHom
    { toFun := A.homogeneousPicardPresheaf.map f
      map_one' := Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map f.unop))
      map_mul' q r := Subtype.ext (SchemePullback.Construction.pullbackClass_mul ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map f.unop) q.val r.val) }
  map_id T := by
    ext q
    exact A.homogeneousPicardPresheaf.map_id_apply T q
  map_comp f h := by
    ext q
    exact A.homogeneousPicardPresheaf.map_comp_apply f h q

def homogeneousPicardGroupInclusion : homogeneousPicardGroupPresheaf A ⟶
    RelativeGroup.Construction.relativePicardGroupPresheaf A.scheme where
  app T := CommGrpCat.ofHom (homogeneousPicardSubgroup A T.unop).subtype
  naturality {T U} f := by ext q; rfl

instance homogeneousPicardSectionsCommGroup (T : (Over S)ᵒᵖ) :
    CommGroup (A.homogeneousPicardSheaf.obj.obj T) :=
  GroupSheafification.Construction.picardTypeSheafifyCommGroup (homogeneousPicardGroupPresheaf A) T

def homogeneousPicardSheafInclusionHom (T : Over S) :
    A.homogeneousPicardSheaf.obj.obj (op T) →* AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme T :=
  GroupSheafMaps.Construction.picardTypeSheafifyMapHom (homogeneousPicardGroupInclusion A) (op T)

theorem homogeneousPicardSheafInclusionHom_apply (T : Over S)
    (q : A.homogeneousPicardSheaf.obj.obj (op T)) :
    homogeneousPicardSheafInclusionHom A T q = A.homogeneousPicardSheafInclusion.hom.app (op T) q :=
  GroupSheafMaps.Construction.picardTypeSheafifyMapHom_apply (homogeneousPicardGroupInclusion A) (op T) q

theorem trivialHomogeneousPicardClass_eq_one (T : Over S) :
    A.trivialHomogeneousPicardClass T = 1 :=
  (GroupSheafification.Construction.picardTypeSheafifyUnitHom (homogeneousPicardGroupPresheaf A) (op T)).map_one

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousGroup
