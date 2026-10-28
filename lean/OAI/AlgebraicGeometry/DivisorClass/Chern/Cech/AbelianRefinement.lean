import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.LocalSections

/-! # Abelian Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.AbelianRefinement

noncomputable section

section

/-! Refinement of actual abelian Cech cochains preserves differentials and coefficients. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I J : Type} (U : I → Opens X) (V : J → Opens X)
  (r : J → I) (hr : ∀ j, V j ≤ U (r j))

def abelianCechRefinementMap (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ) :
    Abelian.CechCoordinates.AbelianCechCochain F U n →+ Abelian.CechCoordinates.AbelianCechCochain F V n where
  toFun k a := F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le U V r hr a)).op (k (r ∘ a))
  map_zero' := by funext a; exact map_zero _
  map_add' k l := by funext a; exact map_add _ _ _

theorem abelianCechRefinementMap_delta (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F U n) :
    abelianCechRefinementMap U V r hr F (n + 1) (Abelian.CechCoordinates.abelianCechDelta F U n k) =
      Abelian.CechCoordinates.abelianCechDelta F V n (abelianCechRefinementMap U V r hr F n k) := by
  funext a
  change F.map _ (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • F.map _ (k ((r ∘ a) ∘ j.succAbove))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  congr 1
  change F.map _ (F.map _ (k (r ∘ a ∘ j.succAbove))) =
    F.map _ (F.map _ (k (r ∘ a ∘ j.succAbove)))
  apply ConcreteCategory.congr_hom
    (show F.map _ ≫ F.map _ = F.map _ ≫ F.map _ from by
      rw [← F.map_comp, ← F.map_comp]
      congr 1)

theorem abelianCechRefinementMap_coefficient
    {F G : X.Presheaf AddCommGrpCat.{0}} (f : F ⟶ G) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F U n) :
    Abelian.CechClasses.abelianCechCoefficient V f n (abelianCechRefinementMap U V r hr F n k) =
      abelianCechRefinementMap U V r hr G n (Abelian.CechClasses.abelianCechCoefficient U f n k) := by
  funext a
  exact ConcreteCategory.congr_hom
    (f.naturality (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le U V r hr a)).op) (k (r ∘ a))

end

/-! The actual restriction map between native Cech complexes for a refinement of covers. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I J : Type} (U : I → Opens X) (V : J → Opens X)
  (r : J → I) (hr : ∀ j, V j ≤ U (r j))

def nativeCechRefinementComponent (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj F).X n ⟶
      ((CategoryTheory.cechComplexFunctor V).obj F).X n :=
  AddCommGrpCat.ofHom ((Abelian.CechCoordinates.abelianCechCoordinates F V n).symm.toAddMonoidHom.comp
    ((abelianCechRefinementMap U V r hr F n).comp (Abelian.CechCoordinates.abelianCechCoordinates F U n).toAddMonoidHom))

theorem nativeCechRefinementComponent_coordinates (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (x : ((CategoryTheory.cechComplexFunctor U).obj F).X n) :
    Abelian.CechCoordinates.abelianCechCoordinates F V n (nativeCechRefinementComponent U V r hr F n x) =
      abelianCechRefinementMap U V r hr F n (Abelian.CechCoordinates.abelianCechCoordinates F U n x) :=
  (Abelian.CechCoordinates.abelianCechCoordinates F V n).apply_symm_apply _

def nativeCechRefinement (F : X.Presheaf AddCommGrpCat.{0}) :
    (CategoryTheory.cechComplexFunctor U).obj F ⟶ (CategoryTheory.cechComplexFunctor V).obj F :=
  CochainComplex.ofHom (nativeCechRefinementComponent U V r hr F) (fun n => by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply (Abelian.CechCoordinates.abelianCechCoordinates F V (n + 1)).injective
    change Abelian.CechCoordinates.abelianCechCoordinates F V (n + 1)
      (((CategoryTheory.cechComplexFunctor V).obj F).d n (n + 1)
        (nativeCechRefinementComponent U V r hr F n x)) =
      Abelian.CechCoordinates.abelianCechCoordinates F V (n + 1)
        (nativeCechRefinementComponent U V r hr F (n + 1)
          (((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1) x))
    rw [Abelian.CechCoordinates.abelianCechCoordinates_d, nativeCechRefinementComponent_coordinates,
      nativeCechRefinementComponent_coordinates, Abelian.CechCoordinates.abelianCechCoordinates_d,
      abelianCechRefinementMap_delta])

theorem nativeCechRefinement_naturality {F G : X.Presheaf AddCommGrpCat.{0}} (f : F ⟶ G) :
    ((CategoryTheory.cechComplexFunctor U).map f) ≫ nativeCechRefinement U V r hr G =
      nativeCechRefinement U V r hr F ≫ ((CategoryTheory.cechComplexFunctor V).map f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply (Abelian.CechCoordinates.abelianCechCoordinates G V n).injective
  change Abelian.CechCoordinates.abelianCechCoordinates G V n
    (nativeCechRefinementComponent U V r hr G n (((CategoryTheory.cechComplexFunctor U).map f).f n x)) =
    Abelian.CechCoordinates.abelianCechCoordinates G V n (((CategoryTheory.cechComplexFunctor V).map f).f n
      (nativeCechRefinementComponent U V r hr F n x))
  rw [nativeCechRefinementComponent_coordinates]
  have he : Abelian.CechCoordinates.abelianCechCoordinates G U n (((CategoryTheory.cechComplexFunctor U).map f).f n x) =
      Abelian.CechClasses.abelianCechCoefficient U f n (Abelian.CechCoordinates.abelianCechCoordinates F U n x) := by
    funext a
    exact Abelian.CechCoordinates.abelianCechCoordinates_naturality F U f n x a
  rw [he, ← abelianCechRefinementMap_coefficient]
  funext a
  rw [Abelian.CechCoordinates.abelianCechCoordinates_naturality, nativeCechRefinementComponent_coordinates]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.AbelianRefinement
