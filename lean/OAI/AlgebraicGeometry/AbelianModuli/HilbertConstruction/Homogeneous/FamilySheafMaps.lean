import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilyMaps

/-! # Family Sheaf Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilySheafMaps

noncomputable section

/-! Homogeneous Picard sheaf maps preserve actual bundle classes and the origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}

/-- Pullback on homogeneous Picard sheaves along a group-scheme morphism. -/
def homogeneousPicardSheafFamilyMap (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    B.homogeneousPicardSheaf ⟶ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map (FamilyMaps.homogeneousPicardPresheafMap f)

/-- Family pullback on homogeneous Picard sheaves agrees with actual bundle pullback. -/
theorem homogeneousPicardSheafFamilyMap_toSheafify (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (T : Over S) (q : B.homogeneousPicardPresheaf.obj (.op T)) :
    (homogeneousPicardSheafFamilyMap f).hom.app (.op T)
      ((toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf).app (.op T) q) =
    (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T)
      ((FamilyMaps.homogeneousPicardPresheafMap f).app (.op T) q) :=
  (ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Scheme.fppfTopology.over S)
      (FamilyMaps.homogeneousPicardPresheafMap f)) (.op T)) q).symm

/-- The trivial homogeneous Picard class is fixed by family pullback. -/
theorem homogeneousPicardSheafFamilyMap_trivial (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (T : Over S) :
    (homogeneousPicardSheafFamilyMap f).hom.app (.op T) (B.trivialHomogeneousPicardClass T) =
      A.trivialHomogeneousPicardClass T := by
  let q : B.homogeneousPicardPresheaf.obj (.op T) :=
    ⟨Line.Bundles.LineBundle.trivialClass ((Picard.PicardSheaf.familySchemeFunctor B.scheme).obj T), B.trivialClass_homogeneous T⟩
  have hq : (FamilyMaps.homogeneousPicardPresheafMap f).app (.op T) q =
      (⟨Line.Bundles.LineBundle.trivialClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T), A.trivialClass_homogeneous T⟩ :
        A.homogeneousPicardPresheaf.obj (.op T)) := by
    apply Subtype.ext
    exact Line.Bundles.LineBundle.pullbackClass_trivial ((Picard.FamilyMaps.familySchemeMap f).app T)
  exact (homogeneousPicardSheafFamilyMap_toSheafify f T q).trans
    (congrArg (fun q' =>
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T) q') hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilySheafMaps
