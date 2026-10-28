import OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent

/-! # Parameterized Homogeneous Picard -/

namespace OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

noncomputable section

/-! A proved homogeneous parameter family gives natural sections of
the actual homogeneous Picard sheaf, with its normalized origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {P : Over S}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (hQ : A.IsHomogeneousPicardClass P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))

def parameterHomogeneousClass {T : Over S} (t : T ⟶ P) : A.homogeneousPicardPresheaf.obj (.op T) :=
  ⟨ParameterizedPicardClass.parameterLineClass Q t, hQ.pullback A t⟩

theorem parameterHomogeneousClass_naturality {T U : Over S} (t : T ⟶ P) (u : U ⟶ T) :
    A.homogeneousPicardPresheaf.map u.op (parameterHomogeneousClass A Q hQ t) =
      parameterHomogeneousClass A Q hQ (u ≫ t) := by
  apply Subtype.ext
  exact ParameterizedPicardClass.parameterLineClass_naturality Q t u

def parameterHomogeneousPicardClass {T : Over S} (t : T ⟶ P) :
    A.homogeneousPicardSheaf.obj.obj (.op T) :=
  (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T)
    (parameterHomogeneousClass A Q hQ t)

theorem parameterHomogeneousPicardClass_naturality {T U : Over S} (t : T ⟶ P) (u : U ⟶ T) :
    A.homogeneousPicardSheaf.obj.map u.op (parameterHomogeneousPicardClass A Q hQ t) =
      parameterHomogeneousPicardClass A Q hQ (u ≫ t) := by
  exact ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).naturality_apply
    u.op (parameterHomogeneousClass A Q hQ t)).symm.trans
      (congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op U))
        (parameterHomogeneousClass_naturality A Q hQ t u))

theorem parameterHomogeneousPicardClass_one [GrpObj P]
    (e : (Q.pullback (lift (1 : A.scheme ⟶ P) (𝟙 A.scheme)).left).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) (T : Over S) :
    parameterHomogeneousPicardClass A Q hQ (1 : T ⟶ P) = A.trivialHomogeneousPicardClass T := by
  apply congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T))
  apply Subtype.ext
  exact ParameterizedPicardClass.parameterLineClass_one Q e T

def homogeneousParameterMap : uliftYoneda.{u + 1}.obj P ⟶ A.homogeneousPicardSheaf.obj where
  app _ := TypeCat.ofHom (fun t => parameterHomogeneousPicardClass A Q hQ t.down)
  naturality := by
    intro T U f
    ext t
    exact (parameterHomogeneousPicardClass_naturality A Q hQ t.down f.unop).symm

theorem parameterHomogeneousPicardClass_forget {T : Over S} (t : T ⟶ P) :
    A.homogeneousPicardSheafInclusion.hom.app (.op T) (parameterHomogeneousPicardClass A Q hQ t) =
      ParameterizedPicardClass.parameterPicardClass Q t := by
  have H := (ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Scheme.fppfTopology.over S)
      A.homogeneousPicardInclusion) (.op T)) (parameterHomogeneousClass A Q hQ t)).symm
  exact H

end

end OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard
