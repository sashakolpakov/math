import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterBaseChange

/-! # Parameter Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterFunctoriality

noncomputable section

/-! The geometric maps between the original family pullbacks preserve identities and composition exactly. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem singleParameterBaseChangeMap_over {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A : Over S) :
    ParameterBaseChange.singleParameterBaseChangeMap f A ≫ ((Over.pullback M.hom).obj A).hom =
      ((Over.pullback T.hom).obj A).hom ≫ f.left :=
  (ParameterBaseChange.singleParameterBaseChangeMap_isPullback f A).w

theorem singleParameterBaseChangeMap_id {S : Scheme.{u}} (T : Over S) (A : Over S) :
    ParameterBaseChange.singleParameterBaseChangeMap (𝟙 T) A = 𝟙 ((Over.pullback T.hom).obj A).left := by
  symm
  apply Cartesian.BaseChangeMap.cartesianBaseChangeMap_unique
  · simp
  · simp

theorem singleParameterBaseChangeMap_composition {S : Scheme.{u}} {U T M : Over S}
    (f : U ⟶ T) (g : T ⟶ M) (A : Over S) :
    ParameterBaseChange.singleParameterBaseChangeMap (f ≫ g) A = ParameterBaseChange.singleParameterBaseChangeMap f A ≫ ParameterBaseChange.singleParameterBaseChangeMap g A := by
  apply (IsPullback.of_hasPullback A.hom M.hom).hom_ext
  · rw [ParameterBaseChange.singleParameterBaseChangeMap_comp, Category.assoc, ParameterBaseChange.singleParameterBaseChangeMap_comp,
      ParameterBaseChange.singleParameterBaseChangeMap_comp]
  · change ParameterBaseChange.singleParameterBaseChangeMap (f ≫ g) A ≫ ((Over.pullback M.hom).obj A).hom =
      (ParameterBaseChange.singleParameterBaseChangeMap f A ≫ ParameterBaseChange.singleParameterBaseChangeMap g A) ≫ ((Over.pullback M.hom).obj A).hom
    rw [singleParameterBaseChangeMap_over, Category.assoc, singleParameterBaseChangeMap_over,
      ← Category.assoc, singleParameterBaseChangeMap_over, Category.assoc]
    rfl

theorem singleParameterBaseChangeIso_hom_fst {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A : Over S) :
    (ParameterBaseChange.singleParameterBaseChangeIso f A).hom.left ≫ pullback.fst ((Over.pullback M.hom).obj A).hom f.left =
      ParameterBaseChange.singleParameterBaseChangeMap f A :=
  (ParameterBaseChange.singleParameterBaseChangeMap_isPullback f A).isoPullback_hom_fst

theorem singleParameterBaseChangeIso_inv_comp {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A : Over S) :
    (ParameterBaseChange.singleParameterBaseChangeIso f A).inv.left ≫ ParameterBaseChange.singleParameterBaseChangeMap f A =
      pullback.fst ((Over.pullback M.hom).obj A).hom f.left :=
  (ParameterBaseChange.singleParameterBaseChangeMap_isPullback f A).isoPullback_inv_fst

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterFunctoriality
