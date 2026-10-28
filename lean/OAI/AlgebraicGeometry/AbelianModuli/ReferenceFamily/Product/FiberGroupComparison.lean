import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupPointNormalization

/-! # Fiber Group Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.FiberGroupComparison

/-! A natural product-fiber comparison between Cartesian monoidal
functors preserves the actual induced group-object structures. -/

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] [G.Monoidal] (n : F ⋙ G ≅ 𝟭 C)
    (A : C) [GrpObj A]

def productFiberComparisonMonIso : Mon.mk (G.obj (F.obj A)) ≅ Mon.mk A :=
  (Functor.mapMonCompIso (F := F) (G := G)).symm.app (Mon.mk A) ≪≫
    (Functor.mapMonNatIso n).app (Mon.mk A) ≪≫ (Functor.mapMonIdIso (C := C)).app (Mon.mk A)

theorem productFiberComparisonMonIso_hom :
    (productFiberComparisonMonIso F G n A).hom.hom = n.hom.app A := by
  let f : G.obj (F.obj A) ⟶ A := n.hom.app A
  change (𝟙 (G.obj (F.obj A))) ≫ f ≫ 𝟙 A = f
  rw [Category.id_comp, Category.comp_id]

theorem productFiberComparison_isMonHom : IsMonHom (show G.obj (F.obj A) ⟶ A from n.hom.app A) := by
  have h : IsMonHom (productFiberComparisonMonIso F G n A).hom.hom := inferInstance
  exact (congrArg (fun f => IsMonHom f) (productFiberComparisonMonIso_hom F G n A)).mp h

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.FiberGroupComparison
