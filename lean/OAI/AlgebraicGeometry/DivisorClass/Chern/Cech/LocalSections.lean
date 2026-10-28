import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.IntrinsicOperators
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle

/-! # Local Sections -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.LocalSections

noncomputable section

/-! Families of actual local sections and their literal Cech differences. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem abelianCechDelta_delta (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (b : Abelian.CechCoordinates.AbelianCechCochain F U n) :
    Abelian.CechCoordinates.abelianCechDelta F U (n + 1) (Abelian.CechCoordinates.abelianCechDelta F U n b) = 0 := by
  let C := (CategoryTheory.cechComplexFunctor U).obj F
  have hd := ConcreteCategory.congr_hom (C.d_comp_d n (n + 1) (n + 2))
    ((Abelian.CechCoordinates.abelianCechCoordinates F U n).symm b)
  change C.d (n + 1) (n + 2) (C.d n (n + 1) ((Abelian.CechCoordinates.abelianCechCoordinates F U n).symm b)) = 0 at hd
  have h := congrArg (Abelian.CechCoordinates.abelianCechCoordinates F U (n + 2)) hd
  dsimp only [C] at h
  rw [Abelian.CechCoordinates.abelianCechCoordinates_d, Abelian.CechCoordinates.abelianCechCoordinates_d, AddEquiv.apply_symm_apply, map_zero] at h
  exact h

theorem abelianCechCoefficient_injective {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) [Mono f] (n : ℕ) :
    Function.Injective (Abelian.CechClasses.abelianCechCoefficient U f.hom n) := by
  intro b c h
  funext a
  exact Chern.Sheaf.TransitionCocycle.sheafMono_section_injective f (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (congrFun h a)

def abelianCechLocalSections (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (s : ∀ i, F.obj.obj (op (U i))) : Abelian.CechCoordinates.AbelianCechCochain F.obj U 0 :=
  fun a => Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (s (a 0))

theorem abelianCechLocalSections_delta (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (s : ∀ i, F.obj.obj (op (U i))) (a : Fin 2 → I) :
    Abelian.CechCoordinates.abelianCechDelta F.obj U 0 (abelianCechLocalSections U F s) a =
      Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) (s (a 1)) -
        Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (s (a 0)) := by
  unfold Abelian.CechCoordinates.abelianCechDelta
  erw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul, ← sub_eq_add_neg]
  change Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F _ (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F _ (s (a 1))) -
    Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F _ (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F _ (s (a 0))) = _
  rw [Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.LocalSections
