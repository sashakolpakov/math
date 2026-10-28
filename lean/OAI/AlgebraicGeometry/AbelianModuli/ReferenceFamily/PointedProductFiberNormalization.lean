import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.FiberGroupComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Pointed Product Fiber Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedProductFiberNormalization

/-! An actual normalized product isomorphism can be made pointed
without changing its actual special-fiber map. -/

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] [G.Monoidal] (n : F ⋙ G ≅ 𝟭 C)
    (X : D) [GrpObj X] (e : X ≅ F.obj (G.obj X))

theorem groupPointNormalizedIso_normalizesProductFiber (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) :
    NormalizedDual.OpenProductData.NormalizesProductFiber F G n (GroupPointNormalization.groupPointNormalizedIso e) := by
  let ni : G.obj (F.obj (G.obj X)) ≅ G.obj X := n.app (G.obj X)
  have : IsMonHom ni.hom := Product.FiberGroupComparison.productFiberComparison_isMonHom F G n (G.obj X)
  have : IsMonHom ni.inv := inferInstance
  have heq : G.map e.hom = ni.inv := by
    apply (cancel_mono ni.hom).mp
    exact he.trans ni.inv_hom_id.symm
  have : IsMonHom (G.map e.hom) := (congrArg (fun f => IsMonHom f) heq).mpr inferInstance
  change G.map (GroupPointNormalization.groupPointNormalizedIso e).hom ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X)
  rw [GroupPointNormalization.groupPointNormalizedIso_map_of_isMonHom G e]
  exact he

theorem exists_pointed_normalizedProduct (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) :
    ∃ e' : X ≅ F.obj (G.obj X), NormalizedDual.OpenProductData.NormalizesProductFiber F G n e' ∧
      η[X] ≫ e'.hom = η[F.obj (G.obj X)] :=
  ⟨GroupPointNormalization.groupPointNormalizedIso e, groupPointNormalizedIso_normalizesProductFiber F G n X e he,
    GroupPointNormalization.groupPointNormalizedIso_point e⟩

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedProductFiberNormalization
