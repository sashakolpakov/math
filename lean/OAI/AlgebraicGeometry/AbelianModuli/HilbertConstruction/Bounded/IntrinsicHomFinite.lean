import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFinitePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicMonoidHom

/-! # Intrinsic Hom Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicHomFinite

noncomputable section

/-! The native homomorphisms of abelian varieties with a fixed embedded graph polynomial form a finite set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)
variable [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem boundedNativeAbelianHom_finite :
    Finite {f : A.scheme ⟶ B.scheme // IsMonHom f ∧ Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P f} := by
  let T := (algSpec (.of K)).obj (Opposite.op (CommAlgCat.of K K))
  have : IsIso T.hom := by
    change IsIso (Spec.map (𝟙 (CommRingCat.of K)))
    infer_instance
  have : Finite (MonoidHomParameters.BoundedFamilyMonoidHom j P T) := HomFinitePoints.boundedAbelianHom_finite_fieldPoints A B j P K
  exact Finite.of_injective (IntrinsicMonoidHom.boundedNativeMonoidHomToPoint j P T)
    (IntrinsicMonoidHom.boundedNativeMonoidHomToPoint_injective j P T)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicHomFinite
