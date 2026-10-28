import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme

/-! # Geometric Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full level structures as actual isomorphisms of group schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {S : Scheme.{u}}

/-- The split ordered-level scheme carries the represented constant group law. -/
instance Geometric.GeometricLevel.constantFullLevelScheme_group (g N : ℕ) (S : Scheme.{u}) :
    GrpObj (Level.Scheme.constantFullLevelScheme g N S) :=
  GrpObj.ofRepresentableBy (Level.Scheme.constantFullLevelScheme g N S)
    (Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S) (Level.Scheme.constantFullLevelRepresentable g N S)

/-- The group-valued Yoneda functor of the split scheme is the constant-level functor. -/
def Geometric.GeometricLevel.constantFullLevelYonedaIso (g N : ℕ) (S : Scheme.{u}) :
    yonedaGrpObj (Level.Scheme.constantFullLevelScheme g N S) ≅ Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S :=
  yonedaGrpObjIsoOfRepresentableBy (Level.Scheme.constantFullLevelScheme g N S)
    (Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S) (Level.Scheme.constantFullLevelRepresentable g N S)

variable {A : Abelian.Schemes.AbelianScheme g S}

/-- Transport full level to the two represented group-valued functors. -/
def Abelian.Schemes.AbelianScheme.FullLevel.yonedaLevelEquiv : A.FullLevel N ≃
    (yonedaGrpObj (Level.Scheme.constantFullLevelScheme g N S) ≅ yonedaGrpObj (A.torsionScheme N)) where
  toFun level := Geometric.GeometricLevel.constantFullLevelYonedaIso g N S ≪≫ level ≪≫ (A.torsionSchemeYonedaIso N).symm
  invFun e := (Geometric.GeometricLevel.constantFullLevelYonedaIso g N S).symm ≪≫ e ≪≫ A.torsionSchemeYonedaIso N
  left_inv level := by
    apply Iso.ext
    change (Geometric.GeometricLevel.constantFullLevelYonedaIso g N S).inv ≫
      (((Geometric.GeometricLevel.constantFullLevelYonedaIso g N S).hom ≫
        (level.hom ≫ (A.torsionSchemeYonedaIso N).inv)) ≫
          (A.torsionSchemeYonedaIso N).hom) = level.hom
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  right_inv e := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]

/-- Full ordered level structures are precisely isomorphisms from the split group scheme
to the actual torsion group scheme. -/
def Abelian.Schemes.AbelianScheme.FullLevel.geometricEquiv : A.FullLevel N ≃
    (Grp.mk (Level.Scheme.constantFullLevelScheme g N S) ≅ Grp.mk (A.torsionScheme N)) :=
  Abelian.Schemes.AbelianScheme.FullLevel.yonedaLevelEquiv.trans ((yonedaGrpFullyFaithful (C := Over S)).isoEquiv
    (X := Grp.mk (Level.Scheme.constantFullLevelScheme g N S)) (Y := Grp.mk (A.torsionScheme N))).symm

/-- The actual isomorphism of group schemes determined by a full level structure. -/
def Abelian.Schemes.AbelianScheme.FullLevel.groupSchemeIso (level : A.FullLevel N) :
    Grp.mk (Level.Scheme.constantFullLevelScheme g N S) ≅ Grp.mk (A.torsionScheme N) :=
  Abelian.Schemes.AbelianScheme.FullLevel.geometricEquiv level

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
