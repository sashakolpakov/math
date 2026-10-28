import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomUnramified
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ParameterFieldPoints
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Hom Finite Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFinitePoints

noncomputable section

/-! Bounded abelian homomorphisms form a finite etale parameter, with finitely many points over every fixed extension field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {K : Type u} [Field K] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)
variable [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem boundedAbelianHomParameter_etale :
    Etale (MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom := by
  have := HomUnramified.boundedAbelianHomParameter_formallyUnramified A B j P
  have := (MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P).locallyFiniteType
  exact Etale.of_formallyUnramified_of_flat _

theorem boundedAbelianHom_finite_fieldPoints (F : Type u) [Field F] [Algebra K F] :
    Finite (MonoidHomParameters.BoundedFamilyMonoidHom j P ((algSpec (.of K)).obj (Opposite.op (CommAlgCat.of K F)))) := by
  have := HomUnramified.boundedAbelianHomParameter_finite A B j P
  have := HilbertConstruction.Finite.ParameterFieldPoints.finiteParameter_fieldPoints (K := K) (F := F) (MonoidHomParameters.boundedFamilyMonoidHomParameter j P)
  exact Finite.of_equiv _ (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFinitePoints
