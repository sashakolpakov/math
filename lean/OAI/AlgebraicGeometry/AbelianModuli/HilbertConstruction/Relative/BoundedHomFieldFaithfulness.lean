import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFiberFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompositeFieldHomFaithfulness

/-! # Bounded Hom Field Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BoundedHomFieldFaithfulness

noncomputable section

/-! On a connected test scheme whose structural map factors through a field, bounded relative abelian homomorphisms are determined by one field-valued point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

theorem relativeBoundedAbelianHomParameter_field_faithful
    {S : Scheme.{u}} [IsNoetherian S] {K F : Type u} [Field K] [Field F] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion j.left] (P : Polynomial ℚ)
    (k : Spec (.of K) ⟶ S) (T : Over (Spec (.of K))) [PreconnectedSpace T.left]
    (s : Spec (.of F) ⟶ T.left)
    (a b : Over.mk (T.hom ≫ k) ⟶ Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameter j P)
    (hab : s ≫ a.left = s ≫ b.left) : a = b := by
  let V : Over S := Over.mk (T.hom ≫ k)
  let W : Over S := Over.mk (s ≫ V.hom)
  let c : W ⟶ V := Over.homMk s rfl
  have hc : c ≫ a = c ≫ b := Over.OverMorphism.ext hab
  let e := Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P V
  let f := (e a).val.val
  let q := (e b).val.val
  have hf : IsMonHom f := (e a).property
  have hq : IsMonHom q := (e b).property
  have he := (Bounded.HomFiberFaithfulness.boundedFamilyMonoidHomPoint_natural j P c a).symm.trans
    ((congrArg (Bounded.MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P W) hc).trans
      (Bounded.HomFiberFaithfulness.boundedFamilyMonoidHomPoint_natural j P c b))
  have hgeom : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c q :=
    congrArg (fun D : Bounded.MonoidHomParameters.BoundedFamilyMonoidHom j P W => D.val.val) he
  have hp : (Over.pullback s).map f = (Over.pullback s).map q :=
    (Geometric.MorphismEquality.geometricFamilyMorphismBaseChange_eq_iff c f q).mp hgeom
  apply e.injective
  apply Subtype.ext
  apply Subtype.ext
  exact @Abelian.Schemes.AbelianScheme.compositePullback_hom_eq_of_field_fiber S T.left K F _ _ g h
    A B k T.hom inferInstance s f q hf hq hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BoundedHomFieldFaithfulness
