import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.PointedMapFieldFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FaithfulPullbackParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeParameterNoetherian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeUnramifiedFieldCriterion

/-! # Pointed Map Unramified -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.PointedMapUnramified

noncomputable section

/-! The actual bounded pointed-map parameter between abelian schemes over a noetherian base is formally unramified, including over nonreduced bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
variable [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem relativeBoundedPointedMapParameter_fieldFiber_faithful
    {K : Type u} [Field K] (k : Spec (.of K) ⟶ S) :
    RigidParameterDiagonal.FieldFaithfulParameter ((Over.pullback k).obj (Bounded.PointedMapParameters.boundedPointedMapParameter j P)) := by
  apply HilbertConstruction.Field.FaithfulPullbackParameter.fieldFaithfulParameter_pullback
  intro F _ T _ s a b hab
  exact PointedMapFieldFaithfulness.relativeBoundedPointedMapParameter_field_faithful A B j P k T s a b hab

theorem relativeBoundedPointedMapParameter_formallyUnramified :
    FormallyUnramified (Bounded.PointedMapParameters.boundedPointedMapParameter j P).hom := by
  let M := Bounded.PointedMapParameters.boundedPointedMapParameter j P
  let Q := Bounded.PointedMapParameters.boundedPointedMapParameterQuasiProjectivePresentation j P
  have ht : LocallyOfFiniteType M.hom := Q.locallyFiniteType
  have hq : QuasiCompact M.hom := Q.quasiCompact
  apply SchemeUnramifiedFieldCriterion.formallyUnramified_of_fieldPullbacks M.hom
  intro K _ k
  have hN : IsNoetherian (pullback ((Over.pullback k).obj M).hom ((Over.pullback k).obj M).hom) :=
    Finite.TypeParameterNoetherian.finiteTypeParameter_pullback_selfProduct_noetherian M k
  exact RigidParameterDiagonal.fieldFaithfulParameter_formallyUnramified ((Over.pullback k).obj M)
    (relativeBoundedPointedMapParameter_fieldFiber_faithful A B j P k)

theorem relativeBoundedPointedMapParameter_open_diagonal :
    IsOpenImmersion (pullback.diagonal (Bounded.PointedMapParameters.boundedPointedMapParameter j P).hom) := by
  have := relativeBoundedPointedMapParameter_formallyUnramified A B j P
  have := (Bounded.PointedMapParameters.boundedPointedMapParameterQuasiProjectivePresentation j P).locallyFiniteType
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.PointedMapUnramified
