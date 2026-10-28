import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PicardMonoid

/-! # Picard Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Multiplicative sections of the homogeneous Picard sheaf and the map from actual homogeneous line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {g : ℕ} {S : Scheme.{u}}

abbrev Abelian.Schemes.AbelianScheme.HomogeneousPicardSections (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :=
  A.homogeneousPicardSheaf.obj.obj (.op T)

instance Abelian.Schemes.AbelianScheme.homogeneousPicardSectionsCommMonoid (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    CommMonoid (A.HomogeneousPicardSections T) :=
  PresheafMonoidSections.presheafSectionsCommMonoid A.homogeneousPicardSheaf.obj (.op T)

def Abelian.Schemes.AbelianScheme.homogeneousPicardSectionRestriction (A : Abelian.Schemes.AbelianScheme g S) {T U : Over S} (f : U ⟶ T) :
    A.HomogeneousPicardSections T →* A.HomogeneousPicardSections U where
  toFun := A.homogeneousPicardSheaf.obj.map f.op
  map_one' := PresheafMonoidSections.presheafSections_map_one A.homogeneousPicardSheaf.obj f.op
  map_mul' := PresheafMonoidSections.presheafSections_map_mul A.homogeneousPicardSheaf.obj f.op

def Abelian.Schemes.AbelianScheme.homogeneousPicardCommMonFunctor (A : Abelian.Schemes.AbelianScheme g S) : (Over S)ᵒᵖ ⥤ CommMonCat.{u + 1} where
  obj T := CommMonCat.of (A.HomogeneousPicardSections T.unop)
  map f := CommMonCat.ofHom (A.homogeneousPicardSectionRestriction f.unop)
  map_id T := by
    apply CommMonCat.hom_ext
    ext q
    exact A.homogeneousPicardSheaf.obj.map_id_apply T q
  map_comp f h := by
    apply CommMonCat.hom_ext
    ext q
    exact A.homogeneousPicardSheaf.obj.map_comp_apply f h q

def Abelian.Schemes.AbelianScheme.toHomogeneousPicard (A : Abelian.Schemes.AbelianScheme g S) :
    A.homogeneousPicardPresheaf ⟶ A.homogeneousPicardSheaf.obj :=
  toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf

instance Abelian.Schemes.AbelianScheme.toHomogeneousPicardIsMonHom (A : Abelian.Schemes.AbelianScheme g S) : IsMonHom A.toHomogeneousPicard :=
  SheafificationMonoids.toSheafifyIsMonHom (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf

theorem Abelian.Schemes.AbelianScheme.toHomogeneousPicard_mul (A : Abelian.Schemes.AbelianScheme g S) (T : Over S)
    (q r : A.homogeneousPicardPresheaf.obj (.op T)) :
    A.toHomogeneousPicard.app (.op T) (q * r) =
      (A.toHomogeneousPicard.app (.op T) q :
        A.HomogeneousPicardSections T) *
        A.toHomogeneousPicard.app (.op T) r :=
  ConcreteCategory.congr_hom (CC := fun X : Type (u + 1) => X)
    (congr_app (IsMonHom.mul_hom A.toHomogeneousPicard)
      (.op T)) (q, r)

@[simp]
theorem Abelian.Schemes.AbelianScheme.trivialHomogeneousPicardClass_eq_one (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    A.trivialHomogeneousPicardClass T = 1 :=
  ConcreteCategory.congr_hom (CC := fun X : Type (u + 1) => X)
    (congr_app (IsMonHom.one_hom A.toHomogeneousPicard)
      (.op T)) PUnit.unit

def Abelian.Schemes.AbelianScheme.homogeneousPicardSectionInclusion (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    A.HomogeneousPicardSections T →* Picard.PicardSheaf.PicardSections A.scheme T where
  toFun := A.homogeneousPicardSheafInclusion.hom.app (.op T)
  map_one' := ConcreteCategory.congr_hom (CC := fun X : Type (u + 1) => X)
    (congr_app (IsMonHom.one_hom A.homogeneousPicardSheafInclusion.hom) (.op T)) PUnit.unit
  map_mul' q r := ConcreteCategory.congr_hom (CC := fun X : Type (u + 1) => X)
    (congr_app (IsMonHom.mul_hom A.homogeneousPicardSheafInclusion.hom) (.op T)) (q, r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
