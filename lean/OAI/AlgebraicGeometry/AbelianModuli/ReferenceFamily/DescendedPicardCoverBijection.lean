import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.PicardUniversal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousParameterRecovery

/-! # Descended Picard Cover Bijection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardCoverBijection

noncomputable section

/-! The descended Poincare parameter map is bijective on every test
over the original base cover, by the original dual universal property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem descendedPicard_parameter_bijective_over_cover
    {S Y : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Y}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : Y ⟶ S)
    (eA : A.scheme ≅ (B.pullback u).scheme) [IsMonHom eA.hom]
    (E : Over S) (eD : D.abelian.scheme ≅ (Over.pullback u).obj E)
    (q : (Over.map u).obj D.abelian.scheme ⟶ E)
    (hq : q.left = CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E eD)
    (J : HilbertConstruction.Line.Bundles.LineBundle (E ⊗ B.scheme).left)
    (hJ : B.IsHomogeneousPicardClass E (HilbertConstruction.Line.Bundles.LineBundle.classOf J))
    (hr : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareFixed.fixedFamilyPoincare D B u eA)) (T : Over Y) :
    Function.Bijective (fun a : (Over.map u).obj T ⟶ E => RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ a) := by
  let ep := CartesianPoints.CartesianFamily.pointsEquiv u D.abelian.scheme E eD T
  let ec := (D.familyTransportRepresentable eA).homEquiv.trans (B.homogeneousPicardBaseChangeEquiv u T)
  have he (a : T ⟶ D.abelian.scheme) : RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ (ep a) = ec a := by
    exact (congrArg (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ)
      (CartesianPoints.CartesianFamily.pointsEquiv_factor u D.abelian.scheme E eD q hq T a)).trans
        ((HomogeneousParameterRecovery.homogeneousParameterClass_of_recovery B J (PoincareFixed.fixedFamilyPoincare D B u eA) hJ
          (PoincareFixed.fixedFamilyPoincare_homogeneous D B u eA) q hr ((Over.map u).map a)).trans
            (Fixed.PicardUniversal.fixedFamilyPoincare_parameterClass D B u eA T a).symm)
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := ep.surjective a
    obtain ⟨b, rfl⟩ := ep.surjective b
    exact congrArg ep (ec.injective ((he a).symm.trans (hab.trans (he b))))
  · intro x
    obtain ⟨a, ha⟩ := ec.surjective x
    exact ⟨ep a, (he a).trans ha⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardCoverBijection
