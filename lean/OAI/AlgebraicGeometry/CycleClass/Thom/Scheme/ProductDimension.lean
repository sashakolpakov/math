import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral

/-! # Product Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductDimension.Constructions

noncomputable section

/-! The dimension sum for genuine products of integral complex schemes,
proved by restricting the actual structure morphism to nonempty affine opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem schemeProduct_dimension (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    letI := ProductIntegral.Constructions.schemeProduct_isIntegral X Y
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (pullback.fst X.hom Y.hom ≫ X.hom) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom + Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  classical
  let := ProductIntegral.Constructions.schemeProduct_isIntegral X Y
  obtain ⟨i, xi, _⟩ := X.left.affineCover.exists_eq (Classical.choice (inferInstance : Nonempty X.left))
  obtain ⟨j, yj, _⟩ := Y.left.affineCover.exists_eq (Classical.choice (inferInstance : Nonempty Y.left))
  let : Nonempty (X.left.affineCover.X i) := ⟨xi⟩
  let : Nonempty (Y.left.affineCover.X j) := ⟨yj⟩
  let : IsIntegral (X.left.affineCover.X i) := isIntegral_of_isOpenImmersion (X.left.affineCover.f i)
  let : IsIntegral (Y.left.affineCover.X j) := isIntegral_of_isOpenImmersion (Y.left.affineCover.f j)
  let A := Over.mk (X.left.affineCover.f i ≫ X.hom)
  let B := Over.mk (Y.left.affineCover.f j ≫ Y.hom)
  let : IsAffine A.left := Scheme.isAffine_affineCover X.left i
  let : IsAffine B.left := Scheme.isAffine_affineCover Y.left j
  let : LocallyOfFiniteType A.hom := inferInstanceAs (LocallyOfFiniteType (X.left.affineCover.f i ≫ X.hom))
  let : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType (Y.left.affineCover.f j ≫ Y.hom))
  let : IsIntegral A.left := inferInstanceAs (IsIntegral (X.left.affineCover.X i))
  let : IsIntegral B.left := inferInstanceAs (IsIntegral (Y.left.affineCover.X j))
  let := Affine.ProductIs.Constructions.affineProduct_isIntegral A B
  let d : pullback A.hom B.hom ⟶ pullback X.hom Y.hom :=
    pullback.map A.hom B.hom X.hom Y.hom (X.left.affineCover.f i) (Y.left.affineCover.f j)
      (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (Category.comp_id _) (Category.comp_id _)
  let : IsOpenImmersion d := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (X.left.affineCover.f i))
    (inferInstance : IsOpenImmersion (Y.left.affineCover.f j)) rfl rfl
  have hd : d ≫ (pullback.fst X.hom Y.hom ≫ X.hom) = pullback.fst A.hom B.hom ≫ A.hom := by
    dsimp only [d]
    rw [← Category.assoc, pullback.map, pullback.lift_fst, Category.assoc]
    rfl
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion d (pullback.fst X.hom Y.hom ≫ X.hom)
  rw [hd] at h
  rw [← h, Affine.ProductDimension.Constructions.affineProduct_dimension A B]
  exact congrArg₂ (· + ·)
    (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (X.left.affineCover.f i) X.hom)
    (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (Y.left.affineCover.f j) Y.hom)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductDimension.Constructions
