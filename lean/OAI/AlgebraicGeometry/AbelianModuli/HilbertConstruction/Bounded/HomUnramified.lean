import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidParameterDiagonal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFiberFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedQuasiFinite

/-! # Hom Unramified -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomUnramified

noncomputable section

/-! The actual bounded homomorphism parameter between abelian varieties is unramified and finite over the ground field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {K : Type u} [Field K] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)
variable [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem boundedAbelianHomParameter_formallyUnramified :
    FormallyUnramified (MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom := by
  let Q := MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P
  have : IsNoetherian (pullback (MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom
      (MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom) := (Q.product Q).noetherian
  apply RigidParameterDiagonal.fieldFaithfulParameter_formallyUnramified
  intro F _ T _ s a b hab
  exact HomFiberFaithfulness.boundedAbelianHomParameter_field_faithful A B j P T s a b hab

theorem boundedAbelianHomParameter_locallyQuasiFinite :
    LocallyQuasiFinite (MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom := by
  have := boundedAbelianHomParameter_formallyUnramified A B j P
  have := (MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P).locallyFiniteType
  exact UnramifiedQuasiFinite.locallyQuasiFinite_of_unramified _

theorem boundedAbelianHomParameter_finite :
    IsFinite (MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom := by
  have := boundedAbelianHomParameter_locallyQuasiFinite A B j P
  have := (MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P).quasiCompact
  exact IsFinite.of_locallyQuasiFinite _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomUnramified
