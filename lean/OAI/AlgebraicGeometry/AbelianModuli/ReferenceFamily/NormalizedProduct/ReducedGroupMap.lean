import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedProductFiberNormalization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MonoidalReductionMultiplication

/-! # Reduced Group Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.ReducedGroupMap

/-! The actual reduced map of a normalized product isomorphism is
a group isomorphism and satisfies the original multiplication square. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] [G.Monoidal] (n : F ⋙ G ≅ 𝟭 C)
    (X : D) [GrpObj X] (e : X ≅ F.obj (G.obj X))

theorem normalizedProduct_reduced_isMonHom (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) : IsMonHom (G.map e.hom) := by
  let ni : G.obj (F.obj (G.obj X)) ≅ G.obj X := n.app (G.obj X)
  have : IsMonHom ni.hom := Product.FiberGroupComparison.productFiberComparison_isMonHom F G n (G.obj X)
  have : IsMonHom ni.inv := inferInstance
  have heq : G.map e.hom = ni.inv := by
    apply (cancel_mono ni.hom).mp
    exact he.trans ni.inv_hom_id.symm
  exact (congrArg (fun f => IsMonHom f) heq).mpr inferInstance

theorem normalizedProduct_reduced_multiplication (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) :
    G.map (μ[X] ≫ e.hom) = G.map ((e.hom ⊗ₘ e.hom) ≫ μ[F.obj (G.obj X)]) := by
  have := normalizedProduct_reduced_isMonHom F G n X e he
  exact MonoidalReductionMultiplication.monoidalMap_multiplication_of_isMonHom G e.hom

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.ReducedGroupMap
