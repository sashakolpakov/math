import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BoundedHomFieldFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FaithfulPullbackParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeParameterNoetherian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeUnramifiedFieldCriterion

/-! # Bounded Hom Unramified -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BoundedHomUnramified

noncomputable section

/-! The actual bounded homomorphism parameter between abelian schemes over a noetherian base is formally unramified, including over nonreduced bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
variable [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem relativeBoundedAbelianHomParameter_fieldFiber_faithful
    {K : Type u} [Field K] (k : Spec (.of K) ⟶ S) :
    RigidParameterDiagonal.FieldFaithfulParameter ((Over.pullback k).obj (Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameter j P)) := by
  apply HilbertConstruction.Field.FaithfulPullbackParameter.fieldFaithfulParameter_pullback
  intro F _ T _ s a b hab
  exact BoundedHomFieldFaithfulness.relativeBoundedAbelianHomParameter_field_faithful A B j P k T s a b hab

theorem relativeBoundedAbelianHomParameter_formallyUnramified :
    FormallyUnramified (Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom := by
  let M := Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameter j P
  let Q := Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P
  have ht : LocallyOfFiniteType M.hom := Q.locallyFiniteType
  have hq : QuasiCompact M.hom := Q.quasiCompact
  apply SchemeUnramifiedFieldCriterion.formallyUnramified_of_fieldPullbacks M.hom
  intro K _ k
  have hN : IsNoetherian (pullback ((Over.pullback k).obj M).hom ((Over.pullback k).obj M).hom) :=
    Finite.TypeParameterNoetherian.finiteTypeParameter_pullback_selfProduct_noetherian M k
  exact RigidParameterDiagonal.fieldFaithfulParameter_formallyUnramified ((Over.pullback k).obj M)
    (relativeBoundedAbelianHomParameter_fieldFiber_faithful A B j P k)

theorem relativeBoundedAbelianHomParameter_open_diagonal :
    IsOpenImmersion (pullback.diagonal (Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom) := by
  have := relativeBoundedAbelianHomParameter_formallyUnramified A B j P
  have := (Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P).locallyFiniteType
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BoundedHomUnramified
