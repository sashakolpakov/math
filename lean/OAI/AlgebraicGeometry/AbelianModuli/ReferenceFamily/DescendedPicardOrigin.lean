import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPoints

/-! # Descended Picard Origin -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardOrigin

noncomputable section

/-! The constructed homogeneous Picard representation sends the
descended dual identity to the trivial class on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S Y : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Y}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : Y ⟶ S)
    (eA : A.scheme ≅ (B.pullback u).scheme) [IsMonHom eA.hom]
    (E : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (eD : D.abelian.scheme ≅ (E.pullback u).scheme) [IsMonHom eD.hom]
    (q : (Over.map u).obj D.abelian.scheme ⟶ E.scheme)
    (hq : q.left = CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E.scheme eD)
    (J : HilbertConstruction.Line.Bundles.LineBundle (E.scheme ⊗ B.scheme).left)
    (hJ : B.IsHomogeneousPicardClass E.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf J))
    (hr : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareFixed.fixedFamilyPoincare D B u eA))

include hq hr in
theorem descendedPicard_parameter_origin_over_cover (T : Over Y) :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ (1 : (Over.map u).obj T ⟶ E.scheme) =
      B.trivialHomogeneousPicardClass ((Over.map u).obj T) := by
  have hz : (Over.map u).map (1 : T ⟶ D.abelian.scheme) ≫ q = 1 :=
    (CartesianPoints.CartesianFamily.pointsEquiv_factor u D.abelian.scheme E.scheme eD q hq T 1).symm.trans
      (CartesianPoints.CartesianFamily.abelian_pointsEquiv_one u D.abelian E eD T)
  exact (congrArg (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ) hz.symm).trans
    ((HomogeneousParameterRecovery.homogeneousParameterClass_of_recovery B J (PoincareFixed.fixedFamilyPoincare D B u eA) hJ
      (PoincareFixed.fixedFamilyPoincare_homogeneous D B u eA) q hr ((Over.map u).map (1 : T ⟶ D.abelian.scheme))).trans
        ((Fixed.PicardUniversal.fixedFamilyPoincare_parameterClass D B u eA T 1).symm.trans
          ((congrArg (B.homogeneousPicardBaseChangeEquiv u T)
            (D.familyTransportRepresentable_origin eA T)).trans
              (B.trivialHomogeneousPicardClass_baseChange u T))))

variable [Flat u] [LocallyOfFinitePresentation u] [Surjective u]

include hq hr in
theorem descendedPicard_parameter_origin (T : Over S) :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ (1 : T ⟶ E.scheme) = B.trivialHomogeneousPicardClass T := by
  let T' := (Over.pullback u).obj T
  let V := (Over.map u).obj T'
  let f : V ⟶ T := Over.homMk (pullback.fst T.hom u) pullback.condition
  have : Flat f.left := inferInstanceAs (Flat (pullback.fst T.hom u))
  have : LocallyOfFinitePresentation f.left := inferInstanceAs (LocallyOfFinitePresentation (pullback.fst T.hom u))
  have : Surjective f.left := inferInstanceAs (Surjective (pullback.fst T.hom u))
  apply RepresentationTheory.Theta.Geometric.FppfPicardLocality.fppfSheaf_map_injective B.homogeneousPicardSheaf f
  have hz : B.homogeneousPicardSheaf.obj.map f.op (B.trivialHomogeneousPicardClass T) =
      B.trivialHomogeneousPicardClass V := by
    rw [B.trivialHomogeneousPicardClass_eq_one, B.trivialHomogeneousPicardClass_eq_one]
    exact (B.homogeneousPicardSectionRestriction f).map_one
  exact (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality B J hJ (1 : T ⟶ E.scheme) f).trans
    ((congrArg (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ) (MonObj.comp_one f)).trans
      ((descendedPicard_parameter_origin_over_cover D B u eA E eD q hq J hJ hr T').trans hz.symm))

theorem descendedPicardRepresentable_origin (T : Over S) :
    (DescendedPicardRepresentation.descendedPicardRepresentable D B u eA E.scheme eD q hq J hJ hr).homEquiv (1 : T ⟶ E.scheme) =
      B.trivialHomogeneousPicardClass T :=
  (DescendedPicardRepresentation.descendedPicardRepresentable_class D B u eA E.scheme eD q hq J hJ hr T 1).trans
    (descendedPicard_parameter_origin D B u eA E eD q hq J hJ hr T)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardOrigin
