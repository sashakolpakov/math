import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # Infimum Functor Limits -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.InfimumFunctorLimits.RingedModules

noncomputable section

/-! Preservation of infima gives the product and pullback preservation required by open-set inverse image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {A B : Type} [SemilatticeInf A] [SemilatticeInf B]

theorem preorder_prod_eq_inf (U V : A) : prod (C := A) U V = U ⊓ V :=
  le_antisymm (le_inf (leOfHom prod.fst) (leOfHom prod.snd))
    (leOfHom (prod.lift (homOfLE inf_le_left) (homOfLE inf_le_right)))

def infPullbackCone {U V W : A} (f : U ⟶ W) (g : V ⟶ W) : PullbackCone f g :=
  PullbackCone.mk (homOfLE (show U ⊓ V ≤ U from inf_le_left))
    (homOfLE inf_le_right) (Subsingleton.elim _ _)

def infPullbackConeIsLimit {U V W : A} (f : U ⟶ W) (g : V ⟶ W) :
    IsLimit (infPullbackCone f g) :=
  PullbackCone.IsLimit.mk _ (fun s => homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

variable (F : A ⥤ B) (hF : ∀ U V, F.obj (U ⊓ V) = F.obj U ⊓ F.obj V)

include hF

theorem infFunctor_prodComparison_isIso (U V : A) : IsIso (prodComparison F U V) := by
  let e : F.obj (U ⨯ V) ≅ F.obj U ⨯ F.obj V := eqToIso (by
    rw [preorder_prod_eq_inf, preorder_prod_eq_inf, hF])
  have h : prodComparison F U V = e.hom := Subsingleton.elim _ _
  exact h.symm ▸ e.isIso_hom

theorem infFunctor_preservesPullback {U V W : A} (f : U ⟶ W) (g : V ⟶ W) :
    PreservesLimit (cospan f g) F := by
  apply preservesLimit_of_preserves_limit_cone (infPullbackConeIsLimit f g)
  refine ((infPullbackCone f g).isLimitMapConeEquiv F).symm ?_
  refine PullbackCone.IsLimit.mk _ (fun s => homOfLE ?_) (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _) (fun _ _ _ _ => Subsingleton.elim _ _)
  change s.pt ≤ F.obj (U ⊓ V)
  rw [hF]
  exact le_inf (leOfHom s.fst) (leOfHom s.snd)

theorem infFunctor_preservesPullbacks : PreservesLimitsOfShape WalkingCospan F where
  preservesLimit {H} := by
    let : PreservesLimit (cospan (H.map WalkingCospan.Hom.inl) (H.map WalkingCospan.Hom.inr)) F :=
      infFunctor_preservesPullback F hF _ _
    exact preservesLimit_of_iso_diagram F (diagramIsoCospan H).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.InfimumFunctorLimits.RingedModules
