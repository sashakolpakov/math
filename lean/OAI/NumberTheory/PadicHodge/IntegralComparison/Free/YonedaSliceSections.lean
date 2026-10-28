import OAI.AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Over

/-! # Yoneda Slice Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaSliceSections

noncomputable section

/-! Free representable sections are the original constant-source sections on the slice. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v u' v'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasCoproducts.{v} A]
  [HasSheafify J A] (U : C) [HasSheafify (J.over U) A] (M : A)

def slice (H : Sheaf (J.over U) A) :
    ((constantSheaf (J.over U) A).obj M ⟶ H) ≃+ (M ⟶ H.obj.obj (op (Over.mk (𝟙 U)))) :=
  (constantSheafAdj (J.over U) A (Over.mkIdTerminal (X := U))).homAddEquiv M H

omit [HasCoproducts.{v} A] [HasSheafify J A] in
theorem slice_natural {H K : Sheaf (J.over U) A} (g : H ⟶ K)
    (a : (constantSheaf (J.over U) A).obj M ⟶ H) :
    slice J U M K (a ≫ g) = slice J U M H a ≫ g.hom.app (op (Over.mk (𝟙 U))) :=
  (constantSheafAdj (J.over U) A (Over.mkIdTerminal (X := U))).homEquiv_naturality_right a g

omit [HasSheafify (J.over U) A] in
theorem free_natural {H K : Sheaf J A} (g : H ⟶ K) (a : Sheaf.freeYoneda J U M ⟶ H) :
    AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv.FreeYonedaAddEquiv.sheaf J U M K (a ≫ g) =
      AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv.FreeYonedaAddEquiv.sheaf J U M H a ≫ g.hom.app (op U) := by
  change (presheafToSheaf J A).obj (Presheaf.freeYoneda U M) ⟶ H at a
  change Presheaf.freeYonedaHomEquiv ((sheafificationAdjunction J A).homEquiv _ K (a ≫ g)) = _
  rw [(sheafificationAdjunction J A).homEquiv_naturality_right, Presheaf.freeYonedaHomEquiv_comp]
  rfl

def homEquiv (H : Sheaf J A) :
    (Sheaf.freeYoneda J U M ⟶ H) ≃+
      ((constantSheaf (J.over U) A).obj M ⟶ (J.overPullback A U).obj H) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv.FreeYonedaAddEquiv.sheaf J U M H).trans
    (slice J U M ((J.overPullback A U).obj H)).symm

theorem slice_homEquiv (H : Sheaf J A) (a : Sheaf.freeYoneda J U M ⟶ H) :
    slice J U M ((J.overPullback A U).obj H) (YonedaSliceSections.homEquiv J U M H a) =
      AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv.FreeYonedaAddEquiv.sheaf J U M H a :=
  (slice J U M ((J.overPullback A U).obj H)).apply_symm_apply _

theorem homEquiv_natural {H K : Sheaf J A} (g : H ⟶ K)
    (a : Sheaf.freeYoneda J U M ⟶ H) :
    YonedaSliceSections.homEquiv J U M K (a ≫ g) = YonedaSliceSections.homEquiv J U M H a ≫ (J.overPullback A U).map g := by
  apply (slice J U M ((J.overPullback A U).obj K)).injective
  exact (slice_homEquiv J U M K (a ≫ g)).trans
    ((free_natural J U M g a).trans
      ((congrArg (fun b => b ≫ g.hom.app (op U)) (slice_homEquiv J U M H a).symm).trans
        (slice_natural J U M ((J.overPullback A U).map g) (YonedaSliceSections.homEquiv J U M H a)).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaSliceSections
