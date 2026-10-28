import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PicardProducts

/-! # Picard Monoid -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor multiplication on the homogeneous Picard presheaf and its inclusion in the relative Picard presheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {g : ℕ} {S : Scheme.{u}}

instance Abelian.Schemes.AbelianScheme.homogeneousPicardPresheafMonObj (A : Abelian.Schemes.AbelianScheme g S) : MonObj A.homogeneousPicardPresheaf where
  one :=
    { app T := TypeCat.ofHom (fun _ => (1 : A.homogeneousPicardPresheaf.obj T))
      naturality {T U} f := by
        apply ConcreteCategory.ext_apply
        intro q
        apply Subtype.ext
        exact (Line.Bundles.LineBundle.pullbackClass_trivial ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f.unop)).symm }
  mul :=
    { app T := TypeCat.ofHom (fun p => p.1 * p.2)
      naturality {T U} f := by
        apply ConcreteCategory.ext_apply
        intro q
        apply Subtype.ext
        exact (Homogeneous.PicardProducts.relativePicardPresheaf_map_mul A.scheme f.unop q.1.val q.2.val).symm }
  one_mul := by
    ext T q
    exact one_mul q.2
  mul_one := by
    ext T q
    exact mul_one q.1
  mul_assoc := by
    ext T q
    exact mul_assoc q.1.1 q.1.2 q.2

instance Abelian.Schemes.AbelianScheme.homogeneousPicardPresheafIsCommMonObj (A : Abelian.Schemes.AbelianScheme g S) :
    IsCommMonObj A.homogeneousPicardPresheaf where
  mul_comm := by
    ext T q
    exact mul_comm q.2 q.1

instance Abelian.Schemes.AbelianScheme.homogeneousPicardInclusionIsMonHom (A : Abelian.Schemes.AbelianScheme g S) :
    IsMonHom A.homogeneousPicardInclusion where
  one_hom := by
    ext T q
    rfl
  mul_hom := by
    ext T q
    rfl

instance Abelian.Schemes.AbelianScheme.homogeneousPicardSheafMonObj (A : Abelian.Schemes.AbelianScheme g S) : MonObj A.homogeneousPicardSheaf.obj :=
  SheafificationMonoids.sheafifyMonObj (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf

instance Abelian.Schemes.AbelianScheme.homogeneousPicardSheafIsCommMonObj (A : Abelian.Schemes.AbelianScheme g S) :
    IsCommMonObj A.homogeneousPicardSheaf.obj :=
  SheafificationMonoids.sheafifyIsCommMonObj (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf

instance Abelian.Schemes.AbelianScheme.homogeneousPicardSheafInclusionIsMonHom (A : Abelian.Schemes.AbelianScheme g S) :
    IsMonHom A.homogeneousPicardSheafInclusion.hom :=
  SheafificationMonoids.sheafifyMapIsMonHom (Scheme.fppfTopology.over S) A.homogeneousPicardInclusion

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
