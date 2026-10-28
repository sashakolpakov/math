import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFieldPullbackDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicMonoidHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackMapEquality

/-! # Bounded Hom Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.BoundedHomFieldDetection

noncomputable section

/-! Native bounded homomorphisms of abelian schemes over a noetherian base are determined by their field-valued pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem nativeBoundedAbelianHom_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion j.left] (P : Polynomial ℚ)
    (f q : A.scheme ⟶ B.scheme) [IsMonHom f] [IsMonHom q]
    (hf : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P f)
    (hq : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P q)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let f' : Bounded.IntrinsicMonoidHom.BoundedNativeMonoidHom j P := ⟨f, inferInstance, hf⟩
  let q' : Bounded.IntrinsicMonoidHom.BoundedNativeMonoidHom j P := ⟨q, inferInstance, hq⟩
  let T : Over S := Over.mk (𝟙 S)
  have : IsIso T.hom := inferInstanceAs (IsIso (𝟙 S))
  have H : Bounded.IntrinsicMonoidHom.boundedNativeMonoidHomToPoint j P T f' = Bounded.IntrinsicMonoidHom.boundedNativeMonoidHomToPoint j P T q' := by
    apply Bounded.HomFieldPullbackDetection.boundedAbelianHom_eq_of_fieldPullbacks A B j P
    intro K _ s
    change (Over.pullback s).map ((Over.pullback (𝟙 S)).map f) =
      (Over.pullback s).map ((Over.pullback (𝟙 S)).map q)
    apply (Iterated.PullbackMapEquality.overPullback_map_eq_iff_iterated s (𝟙 S) f q).mp
    exact h K (s ≫ 𝟙 S)
  exact congrArg Subtype.val ((Bounded.IntrinsicMonoidHom.boundedNativeMonoidHomToPoint_injective j P T) H)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.BoundedHomFieldDetection
