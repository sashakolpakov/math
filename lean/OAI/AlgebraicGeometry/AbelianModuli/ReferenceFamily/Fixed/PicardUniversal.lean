import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixed
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PoincareClasses
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Picard Universal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.PicardUniversal

noncomputable section

/-! On the original base cover the fixed-family Poincare class is the
original dual universal class, through native family and base comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S Y : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Y}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : Y ⟶ S)
    (e : A.scheme ≅ (B.pullback u).scheme) [IsMonHom e.hom]

theorem fixedFamilyPoincare_rawClass_comparison :
    (B.homogeneousPicardPresheafBaseChangeIso u).hom.app (.op D.abelian.scheme)
      (D.familyTransport e).poincareClass =
    (⟨HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareFixed.fixedFamilyPoincare D B u e), PoincareFixed.fixedFamilyPoincare_homogeneous D B u e⟩ :
      B.homogeneousPicardPresheaf.obj (.op ((Over.map u).obj D.abelian.scheme))) :=
  Subtype.ext rfl

theorem fixedFamilyPoincare_universalClass :
    B.homogeneousPicardBaseChangeEquiv u D.abelian.scheme
      ((D.familyTransportRepresentable e).homEquiv (𝟙 D.abelian.scheme)) =
    (toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf).app
      (.op ((Over.map u).obj D.abelian.scheme))
        ⟨HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareFixed.fixedFamilyPoincare D B u e), PoincareFixed.fixedFamilyPoincare_homogeneous D B u e⟩ := by
  exact (congrArg (B.homogeneousPicardBaseChangeEquiv u D.abelian.scheme)
    (D.familyTransportPoincare_universalClass e)).trans
      ((B.toHomogeneousPicard_baseChange_apply u D.abelian.scheme (D.familyTransport e).poincareClass).trans
        (congrArg ((toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf).app
          (.op ((Over.map u).obj D.abelian.scheme))) (fixedFamilyPoincare_rawClass_comparison D B u e)))

theorem fixedFamilyPoincare_parameterClass (T : Over Y) (a : T ⟶ D.abelian.scheme) :
    B.homogeneousPicardBaseChangeEquiv u T ((D.familyTransportRepresentable e).homEquiv a) =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B (PoincareFixed.fixedFamilyPoincare D B u e)
        (PoincareFixed.fixedFamilyPoincare_homogeneous D B u e) ((Over.map u).map a) := by
  let r := (D.familyTransport e).poincareClass
  let c := (B.homogeneousPicardPresheafBaseChangeIso u).hom
  let b := (toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf).app
    (.op ((Over.map u).obj T))
  have he := (D.familyTransport e).pointClass_eq_poincare a
  have hn := c.naturality_apply a.op r
  have hr := fixedFamilyPoincare_rawClass_comparison D B u e
  exact (congrArg (B.homogeneousPicardBaseChangeEquiv u T) he).trans
    ((B.toHomogeneousPicard_baseChange_apply u T ((B.pullback u).homogeneousPicardPresheaf.map a.op r)).trans
      ((congrArg b hn).trans
        (congrArg (fun x => b (B.homogeneousPicardPresheaf.map ((Over.map u).map a).op x)) hr)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.PicardUniversal
