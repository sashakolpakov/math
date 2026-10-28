import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.AbelianRefinement
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.GlobalCoordinates

/-! # Refinement Global -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.RefinementGlobal

noncomputable section

section

/-! Native refinement preserves restriction of the same actual global section. -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I J : Type} (U : I → Opens X) (V : J → Opens X)
  (r : J → I) (hr : ∀ j, V j ≤ U (r j))

theorem nativeCechRefinement_global (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U ≫ (AbelianRefinement.nativeCechRefinement U V r hr F.obj).f 0 =
      SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F V := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply (Abelian.CechCoordinates.abelianCechCoordinates F.obj V 0).injective
  funext a
  change Abelian.CechCoordinates.abelianCechCoordinates F.obj V 0
    (AbelianRefinement.nativeCechRefinementComponent U V r hr F.obj 0 (SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U x)) a = _
  rw [AbelianRefinement.nativeCechRefinementComponent_coordinates]
  change F.obj.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le U V r hr a)).op
    (Abelian.CechCoordinates.abelianCechCoordinates F.obj U 0 (SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U x) (r ∘ a)) = _
  rw [GlobalCoordinates.abelianCechGlobalAugmentation_coordinates, GlobalCoordinates.abelianCechGlobalAugmentation_coordinates]
  change (F.obj.map _ ≫ F.obj.map _)
    ((CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{0} CategoryTheory.Limits.isTerminalTop).hom.app F x) =
    F.obj.map _ ((CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{0} CategoryTheory.Limits.isTerminalTop).hom.app F x)
  apply ConcreteCategory.congr_hom
  rw [← F.obj.map_comp]
  congr 1

end

/-! Element equations for the unchanged native refinement maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I J : Type} (U : I → Opens X) (V : J → Opens X)
  (r : J → I) (hr : ∀ j, V j ≤ U (r j))

theorem nativeCechRefinement_d (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (x : ((CategoryTheory.cechComplexFunctor U).obj F).X n) :
    ((CategoryTheory.cechComplexFunctor V).obj F).d n (n + 1)
      ((AbelianRefinement.nativeCechRefinement U V r hr F).f n x) =
      (AbelianRefinement.nativeCechRefinement U V r hr F).f (n + 1)
        (((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1) x) :=
  ConcreteCategory.congr_hom ((AbelianRefinement.nativeCechRefinement U V r hr F).comm n (n + 1)) x

theorem nativeCechRefinement_coefficient {F G : X.Presheaf AddCommGrpCat.{0}} (f : F ⟶ G)
    (n : ℕ) (x : ((CategoryTheory.cechComplexFunctor U).obj F).X n) :
    (AbelianRefinement.nativeCechRefinement U V r hr G).f n (((CategoryTheory.cechComplexFunctor U).map f).f n x) =
      ((CategoryTheory.cechComplexFunctor V).map f).f n ((AbelianRefinement.nativeCechRefinement U V r hr F).f n x) :=
  ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n) (AbelianRefinement.nativeCechRefinement_naturality U V r hr f)) x

theorem nativeCechRefinement_symm (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F U n) :
    (AbelianRefinement.nativeCechRefinement U V r hr F).f n ((Abelian.CechCoordinates.abelianCechCoordinates F U n).symm k) =
      (Abelian.CechCoordinates.abelianCechCoordinates F V n).symm (AbelianRefinement.abelianCechRefinementMap U V r hr F n k) := by
  change (Abelian.CechCoordinates.abelianCechCoordinates F V n).symm
    (AbelianRefinement.abelianCechRefinementMap U V r hr F n
      (Abelian.CechCoordinates.abelianCechCoordinates F U n ((Abelian.CechCoordinates.abelianCechCoordinates F U n).symm k))) = _
  rw [AddEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.RefinementGlobal
