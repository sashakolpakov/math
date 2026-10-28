import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalPoincareProductOrigin

/-! # Zero Product -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ZeroProduct.Construction

noncomputable section

/-! The all-test Poincare products specialize at the base origin to
the same original zero-frame multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

universe u

theorem groupLift_one {S : Scheme.{u}} (A B : Over S) [GrpObj A] [GrpObj B] (T : Over S) :
    lift (1 : T ⟶ A) (1 : T ⟶ B) = 1 := by
  apply CartesianMonoidalCategory.hom_ext <;> simp only [lift_fst, lift_snd, MonObj.one_comp]

theorem lineProductParameterLift_one {S : Scheme.{u}} (A X : Over S) [GrpObj A] [GrpObj X] (T : Over S) :
    Universal.LineProducts.Construction.lineProductParameterLift (1 : T ⟶ A ⊗ X) 1 = 1 := by
  simp only [Universal.LineProducts.Construction.lineProductParameterLift, MonObj.one_comp, groupLift_one]

theorem verticalProductParameterLift_one {S : Scheme.{u}} (A X : Over S) [GrpObj A] [GrpObj X] (T : Over S) :
    Universal.VerticalProducts.Construction.verticalProductParameterLift (1 : T ⟶ X ⊗ A) 1 = 1 := by
  simp only [Universal.VerticalProducts.Construction.verticalProductParameterLift, MonObj.one_comp, groupLift_one]

theorem horizontalOneProductRel {S : Scheme.{u}} (A X : Over S) [GrpObj A] [GrpObj X] (T : Over S) :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst A X) (snd A X) (1 : T ⟶ A ⊗ X) 1 1 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [MonObj.one_comp, one_mul]

theorem verticalOneProductRel {S : Scheme.{u}} (A X : Over S) [GrpObj A] [GrpObj X] (T : Over S) :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd X A) (fst X A) (1 : T ⟶ X ⊗ A) 1 1 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [MonObj.one_comp, one_mul]

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

attribute [local instance] GlobalPoincareProductOrigin.Construction.horizontalInputLeft_isMonHom GlobalPoincareProductOrigin.Construction.horizontalInputRight_isMonHom GlobalPoincareProductOrigin.Construction.horizontalOutput_isMonHom
attribute [local instance] GlobalPoincareProductOrigin.Construction.verticalInputLeft_isMonHom GlobalPoincareProductOrigin.Construction.verticalInputRight_isMonHom GlobalPoincareProductOrigin.Construction.verticalOutput_isMonHom

theorem poincareHorizontalProduct_at_zero :
    HorizontalProduct.Construction.poincareHorizontalProduct D (1 : 𝟙_ (Over (Spec (.of k))) ⟶ D.abelian.scheme ⊗ A.scheme) 1 1
      (horizontalOneProductRel D.abelian.scheme A.scheme _) =
        BilinearProducts.Construction.framedLineProduct (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) := by
  have hp : Universal.LineProducts.Construction.lineProductParameterLift (1 : 𝟙_ (Over (Spec (.of k))) ⟶ D.abelian.scheme ⊗ A.scheme) 1 =
      η[HorizontalProduct.Construction.poincareHorizontalParameter D] :=
    (lineProductParameterLift_one D.abelian.scheme A.scheme _).trans (MonObj.one_eq_one _).symm
  let h := horizontalOneProductRel D.abelian.scheme A.scheme (𝟙_ (Over (Spec (.of k))))
  exact (Universal.LineProducts.Construction.pullBilinear_congr_parameter (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _ hp
    (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft D.abelian.scheme A.scheme) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight D.abelian.scheme A.scheme)
    (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint D.abelian.scheme A.scheme) 1 1 1
    (Universal.LineProducts.Construction.lineProductParameterLift_left 1 1) (Universal.LineProducts.Construction.lineProductParameterLift_right 1 1 h.2.1)
    (Universal.LineProducts.Construction.lineProductParameterLift_output 1 1 1 h)
    (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) (HorizontalProduct.Construction.poincareGlobalHorizontalProduct D)).trans
    (GlobalPoincareProductOrigin.Construction.poincareGlobalHorizontalProduct_at_origin D)

theorem poincareVerticalProduct_at_zero :
    VerticalProduct.Construction.poincareVerticalProduct D (1 : 𝟙_ (Over (Spec (.of k))) ⟶ D.abelian.scheme ⊗ A.scheme) 1 1
      (verticalOneProductRel A.scheme D.abelian.scheme _) =
        BilinearProducts.Construction.framedLineProduct (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) := by
  have hp : Universal.VerticalProducts.Construction.verticalProductParameterLift (1 : 𝟙_ (Over (Spec (.of k))) ⟶ D.abelian.scheme ⊗ A.scheme) 1 =
      η[VerticalProduct.Construction.poincareVerticalParameter D] :=
    (verticalProductParameterLift_one A.scheme D.abelian.scheme _).trans (MonObj.one_eq_one _).symm
  let h := verticalOneProductRel A.scheme D.abelian.scheme (𝟙_ (Over (Spec (.of k))))
  exact (Universal.LineProducts.Construction.pullBilinear_congr_parameter (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _ hp
    Universal.VerticalProducts.Construction.verticalInputLeft Universal.VerticalProducts.Construction.verticalInputRight Universal.VerticalProducts.Construction.verticalOutputPoint 1 1 1
    (Universal.VerticalProducts.Construction.verticalProductParameterLift_left 1 1) (Universal.VerticalProducts.Construction.verticalProductParameterLift_right 1 1 h.2.1)
    (Universal.VerticalProducts.Construction.verticalProductParameterLift_output 1 1 1 h)
    (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) (VerticalProduct.Construction.poincareGlobalVerticalProduct D)).trans
    (GlobalPoincareProductOrigin.Construction.poincareGlobalVerticalProduct_at_origin D)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ZeroProduct.Construction
