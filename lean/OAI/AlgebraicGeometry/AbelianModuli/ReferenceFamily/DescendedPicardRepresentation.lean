import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardCoverBijection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafBaseCoverDetection
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Descended Picard Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardRepresentation

noncomputable section

/-! The actual descended Poincare line represents the native homogeneous
Picard sheaf on all test schemes over the quotient base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S Y : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Y}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : Y ⟶ S)
    [Flat u] [LocallyOfFinitePresentation u] [Surjective u]
    (eA : A.scheme ≅ (B.pullback u).scheme) [IsMonHom eA.hom]
    (E : Over S) (eD : D.abelian.scheme ≅ (Over.pullback u).obj E)
    (q : (Over.map u).obj D.abelian.scheme ⟶ E)
    (hq : q.left = CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E eD)
    (J : HilbertConstruction.Line.Bundles.LineBundle (E ⊗ B.scheme).left)
    (hJ : B.IsHomogeneousPicardClass E (HilbertConstruction.Line.Bundles.LineBundle.classOf J))
    (hr : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareFixed.fixedFamilyPoincare D B u eA))

include hq hr in
theorem descendedPicard_parameterMap_isIso : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap B J hJ) := by
  let K := Scheme.fppfTopology.over S
  let f : K.uliftYoneda.{1}.obj E ⟶ B.homogeneousPicardSheaf := ⟨RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap B J hJ⟩
  have hf : IsIso f := by
    apply SheafBaseCoverDetection.sheaf_isIso_of_base_cover u f
    intro T
    have hb := DescendedPicardCoverBijection.descendedPicard_parameter_bijective_over_cover D B u eA E eD q hq J hJ hr T
    constructor
    · intro a b hab
      apply ULift.ext
      exact hb.injective hab
    · intro x
      obtain ⟨a, ha⟩ := hb.surjective x
      exact ⟨ULift.up a, ha⟩
  exact inferInstanceAs (IsIso ((sheafToPresheaf K (Type 1)).map f))

def descendedPicardRepresentable : B.homogeneousPicardSheaf.obj.RepresentableBy E := by
  have : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap B J hJ) := descendedPicard_parameterMap_isIso D B u eA E eD q hq J hJ hr
  exact (Functor.RepresentableBy.equivUliftYonedaIso B.homogeneousPicardSheaf.obj E).symm
    (asIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap B J hJ))

theorem descendedPicardRepresentable_class (T : Over S) (a : T ⟶ E) :
    (descendedPicardRepresentable D B u eA E eD q hq J hJ hr).homEquiv a =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass B J hJ a := rfl

theorem descendedPicardRepresentable_universalClass :
    (descendedPicardRepresentable D B u eA E eD q hq J hJ hr).homEquiv (𝟙 E) =
      (toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf).app (.op E)
        ⟨HilbertConstruction.Line.Bundles.LineBundle.classOf J, hJ⟩ :=
  (descendedPicardRepresentable_class D B u eA E eD q hq J hJ hr E (𝟙 E)).trans
    (HomogeneousParameterRecovery.homogeneousParameterClass_identity B E J hJ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardRepresentation
