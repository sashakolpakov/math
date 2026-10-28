import OAI.RepresentationTheory.Theta.Geometric.HomogeneousPicardUniversality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

/-! # Picard Data -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.PicardData

noncomputable section

/-! The proved isomorphism of the actual homogeneous parameter map
supplies the native dual abelian data, including both normalizations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

universe u
variable {S : Scheme.{u}} {g : ℕ} (A N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.scheme ⊗ A.scheme).left)
    (hQ : A.IsHomogeneousPicardClass N.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    [IsIso (ParameterizedHomogeneousPicard.homogeneousParameterMap A Q hQ)]

def homogeneousParameterRepresentation : A.homogeneousPicardSheaf.obj.RepresentableBy N.scheme :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _).symm (asIso (ParameterizedHomogeneousPicard.homogeneousParameterMap A Q hQ))

theorem homogeneousParameterRepresentation_apply {T : Over S} (a : T ⟶ N.scheme) :
    (homogeneousParameterRepresentation A N Q hQ).homEquiv a =
      ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A Q hQ a := rfl

def dualDataOfHomogeneousParameterIso
    (eA : (Q.pullback (lift (𝟙 N.scheme) (1 : N.scheme ⟶ A.scheme)).left).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.scheme.left)
    (eN : (Q.pullback (lift (1 : A.scheme ⟶ N.scheme) (𝟙 A.scheme)).left).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A where
  abelian := N
  representable := homogeneousParameterRepresentation A N Q hQ
  origin T := ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_one A Q hQ eN T
  poincare := Q
  poincareHomogeneous := hQ
  universalClass := by
    rw [homogeneousParameterRepresentation_apply]
    apply congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op N.scheme))
    apply Subtype.ext
    change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 N.scheme) ⊗ₘ 𝟙 A.scheme).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q
    rw [id_tensorHom_id]
    exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _
  normalizedAtAbelianZero := ⟨eA⟩
  normalizedAtDualZero := ⟨eN⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.PicardData
