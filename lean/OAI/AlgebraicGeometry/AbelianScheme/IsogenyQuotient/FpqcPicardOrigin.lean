import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcDualData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPoints

/-! # Fpqc Picard Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcPicardOrigin.Construction

noncomputable section

/-! The constructed homogeneous Picard representation sends the
descended dual identity to the trivial class on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S Y : Scheme.{0}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : Y ⟶ S)
    (eA : A.scheme ≅ (B.pullback u).scheme) [IsMonHom eA.hom]
    (E : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (eD : D.abelian.scheme ≅ (E.pullback u).scheme) [IsMonHom eD.hom]
    (q : (Over.map u).obj D.abelian.scheme ⟶ E.scheme)
    (hq : q.left = AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E.scheme eD)
    (J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (E.scheme ⊗ B.scheme).left)
    (hJ : B.IsHomogeneousPicardClass E.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J))
    (hr : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare D B u eA))

include hq hr in
theorem fpqc_descendedPicard_parameter_origin_over_cover (T : Over Y) :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ (1 : (Over.map u).obj T ⟶ E.scheme) =
      B.trivialHomogeneousPicardClass ((Over.map u).obj T) := by
  have hz : (Over.map u).map (1 : T ⟶ D.abelian.scheme) ≫ q = 1 :=
    (AbelianModuli.ReferenceFamily.CartesianPoints.CartesianFamily.pointsEquiv_factor u D.abelian.scheme E.scheme eD q hq T 1).symm.trans
      (AbelianModuli.ReferenceFamily.CartesianPoints.CartesianFamily.abelian_pointsEquiv_one u D.abelian E eD T)
  exact (congrArg (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ) hz.symm).trans
    ((AbelianModuli.ReferenceFamily.HomogeneousParameterRecovery.homogeneousParameterClass_of_recovery B J (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare D B u eA) hJ
      (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare_homogeneous D B u eA) q hr ((Over.map u).map (1 : T ⟶ D.abelian.scheme))).trans
        ((AbelianModuli.ReferenceFamily.Fixed.PicardUniversal.fixedFamilyPoincare_parameterClass D B u eA T 1).symm.trans
          ((congrArg (B.homogeneousPicardBaseChangeEquiv u T)
            (D.familyTransportRepresentable_origin eA T)).trans
              (B.trivialHomogeneousPicardClass_baseChange u T))))

variable [Flat u] [QuasiCompact u] [Surjective u]

include hq hr in
set_option backward.isDefEq.respectTransparency false in
theorem fpqc_descendedPicard_parameter_origin
    (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme) (T : Over S) :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ (1 : T ⟶ E.scheme) =
      B.trivialHomogeneousPicardClass T := by
  let T' := (Over.pullback u).obj T
  let V := (Over.map u).obj T'
  let f : V ⟶ T := (Over.mapPullbackAdj u).counit.app T
  apply Picard.BaseCoverInjection.Construction.homogeneousPicard_baseCoverRestriction_injective u B hB T
  have hz : B.homogeneousPicardSheaf.obj.map f.op (B.trivialHomogeneousPicardClass T) =
      B.trivialHomogeneousPicardClass V := by
    let zT : B.homogeneousPicardPresheaf.obj (.op T) :=
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, B.trivialClass_homogeneous T⟩
    let zV : B.homogeneousPicardPresheaf.obj (.op V) :=
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, B.trivialClass_homogeneous V⟩
    have he : B.homogeneousPicardPresheaf.map f.op zT = zV := by
      apply Subtype.ext
      exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor B.scheme).map f)
    exact ((toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf).naturality_apply
      f.op zT).symm.trans (congrArg
        ((toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf).app (.op V)) he)
  exact (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality B J hJ (1 : T ⟶ E.scheme) f).trans
    ((congrArg (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ) (MonObj.comp_one f)).trans
      ((fpqc_descendedPicard_parameter_origin_over_cover D B u eA E eD q hq J hJ hr T').trans hz.symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcPicardOrigin.Construction
