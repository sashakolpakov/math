import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BoundedHomUnramified
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedFieldPointDetection

/-! # Hom Field Pullback Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFieldPullbackDetection

noncomputable section

/-! Actual bounded abelian homomorphism families are determined by all field-valued base changes, including on nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem boundedAbelianHom_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion j.left] (P : Polynomial ℚ) {T : Over S}
    (f q : MonoidHomParameters.BoundedFamilyMonoidHom j P T)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f.val.val = (Over.pullback s).map q.val.val) : f = q := by
  have := Relative.BoundedHomUnramified.relativeBoundedAbelianHomParameter_formallyUnramified A B j P
  have := (MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P).locallyFiniteType
  let e := MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T
  apply e.symm.injective
  apply UnramifiedFieldPointDetection.unramified_overHom_eq_of_fieldPoints
  intro K _ s
  let W : Over S := Over.mk (s ≫ T.hom)
  let c : W ⟶ T := Over.homMk s rfl
  have hc : c ≫ e.symm f = c ≫ e.symm q := by
    apply (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P W).injective
    rw [HomFiberFaithfulness.boundedFamilyMonoidHomPoint_natural, HomFiberFaithfulness.boundedFamilyMonoidHomPoint_natural]
    change (MonoidHomRepresentation.boundedFamilyMonoidHomFunctor j P).map c.op (e (e.symm f)) =
      (MonoidHomRepresentation.boundedFamilyMonoidHomFunctor j P).map c.op (e (e.symm q))
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    exact (Geometric.MorphismEquality.geometricFamilyMorphismBaseChange_eq_iff c f.val.val q.val.val).mpr (h K s)
  exact congrArg Over.Hom.left hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFieldPullbackDetection
