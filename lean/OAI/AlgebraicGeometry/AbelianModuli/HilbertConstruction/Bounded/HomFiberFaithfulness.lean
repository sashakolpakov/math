import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.HomFiberFaithfulness

/-! # Hom Fiber Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFiberFaithfulness

noncomputable section

/-! One field-valued point detects equality of parameter maps into the bounded abelian-homomorphism scheme from a connected test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

theorem boundedFamilyMonoidHomPoint_natural
    {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
    [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom] [MonObj A] [MonObj B]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)
    {U T : Over S} (c : U ⟶ T) (p : T ⟶ MonoidHomParameters.boundedFamilyMonoidHomParameter j P) :
    MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P U (c ≫ p) =
      (MonoidHomRepresentation.boundedFamilyMonoidHomFunctor j P).map c.op (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T p) :=
  ConcreteCategory.congr_hom (CC := fun X : Type u => X)
    ((MonoidHomRepresentation.boundedFamilyMonoidHomClassifyingIso j P).hom.naturality c.op) p

theorem boundedAbelianHomParameter_field_faithful
    {K F : Type u} [Field K] [Field F] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)
    [IsClosedImmersion j.left] (P : Polynomial ℚ)
    (T : Over (Spec (.of K))) [PreconnectedSpace T.left] (s : Spec (.of F) ⟶ T.left)
    (a b : T ⟶ MonoidHomParameters.boundedFamilyMonoidHomParameter j P) (hab : s ≫ a.left = s ≫ b.left) : a = b := by
  let W : Over (Spec (.of K)) := Over.mk (s ≫ T.hom)
  let c : W ⟶ T := Over.homMk s rfl
  have hc : c ≫ a = c ≫ b := Over.OverMorphism.ext hab
  let e := MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T
  let f := (e a).val.val
  let q := (e b).val.val
  have hf : IsMonHom f := (e a).property
  have hq : IsMonHom q := (e b).property
  have he := (boundedFamilyMonoidHomPoint_natural j P c a).symm.trans
    ((congrArg (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P W) hc).trans
      (boundedFamilyMonoidHomPoint_natural j P c b))
  have hgeom : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c q :=
    congrArg (fun D : MonoidHomParameters.BoundedFamilyMonoidHom j P W => D.val.val) he
  have hp : (Over.pullback s).map f = (Over.pullback s).map q :=
    (Geometric.MorphismEquality.geometricFamilyMorphismBaseChange_eq_iff c f q).mp hgeom
  apply e.injective
  apply Subtype.ext
  apply Subtype.ext
  exact @Abelian.Schemes.AbelianScheme.pullback_hom_eq_of_field_fiber K F _ _ g h T.left
    A B T.hom inferInstance s f q hf hq hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFiberFaithfulness
