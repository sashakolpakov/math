import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Naturality
import OAI.RepresentationTheory.Theta.Geometric.TangentScalars
import OAI.AlgebraicGeometry.Albanese.Construction.Smooth

/-! # Tangent Addition -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The extended native tangent coordinates preserve the actual group
operation on geometric dual-number points. -/

open scoped TensorProduct _root_.CategoryTheory.MonObj
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable (F : Type) [Field F] [Algebra ℂ F]
  {X Y Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [MonObj X]
  [IsIntegral Y.left] [Smooth Y.hom] [MonObj Y]
  [IsIntegral Z.left] [Smooth Z.hom]

def TangentAddition.geometricGroupDerivative (f : X ⟶ Y) :
    (F ⊗[ℂ] GroupDerivative.nativeTangentModel X) →ₗ[F] (F ⊗[ℂ] GroupDerivative.nativeTangentModel Y) :=
  (GroupDerivative.nativeGroupDerivative f).toLinearMap.baseChange F

theorem TangentAddition.geometricGroupDerivative_id (v : F ⊗[ℂ] GroupDerivative.nativeTangentModel X) :
    TangentAddition.geometricGroupDerivative F (𝟙 X) v = v := by
  induction v using TensorProduct.inductionOn with
  | add u v hu hv => rw [map_add, hu, hv]
  | tmul c v =>
      change c ⊗ₜ[ℂ] GroupDerivative.nativeGroupDerivative (𝟙 X) v = c ⊗ₜ[ℂ] v
      rw [GroupDerivative.nativeGroupDerivative_id, ContinuousLinearMap.id_apply]

theorem TangentAddition.geometricGroupDerivative_one (v : F ⊗[ℂ] GroupDerivative.nativeTangentModel X) :
    TangentAddition.geometricGroupDerivative F (1 : X ⟶ Y) v = 0 := by
  induction v using TensorProduct.inductionOn with
  | add u v hu hv => rw [map_add, hu, hv, add_zero]
  | tmul c v =>
      change c ⊗ₜ[ℂ] GroupDerivative.nativeGroupDerivative (1 : X ⟶ Y) v = 0
      rw [GroupDerivative.nativeGroupDerivative_one]
      simp only [zero_apply, TensorProduct.tmul_zero]

theorem TangentAddition.geometricGroupDerivative_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) [IsMonHom f]
    (v : F ⊗[ℂ] GroupDerivative.nativeTangentModel X) :
    TangentAddition.geometricGroupDerivative F g (TangentAddition.geometricGroupDerivative F f v) =
      TangentAddition.geometricGroupDerivative F (f ≫ g) v := by
  induction v using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul c v =>
      exact congrArg (fun w : GroupDerivative.nativeTangentModel Z => c ⊗ₜ[ℂ] w)
        (GroupDerivative.nativeGroupDerivative_comp_apply f g v)

theorem Intrinsic.TangentCharts.NativeTangentChart.geometricGroup_naturality (C : Intrinsic.TangentCharts.NativeTangentChart X 1)
    (D : Intrinsic.TangentCharts.NativeTangentChart Y 1) (f : X ⟶ Y) [IsMonHom f] (v : F ⊗[ℂ] GroupDerivative.nativeTangentModel X) :
    (D.geometricTangentEquiv F (TangentAddition.geometricGroupDerivative F f v)).val =
      (C.geometricTangentEquiv F v).val ≫ f :=
  C.geometricTangentEquiv_naturality_of_point F f D (MonObj.one_comp f) v

variable [IsCommMonObj X]

theorem Intrinsic.TangentCharts.NativeTangentChart.geometricTangentEquiv_add (C : Intrinsic.TangentCharts.NativeTangentChart X 1)
    (v w : F ⊗[ℂ] GroupDerivative.nativeTangentModel X) :
    (C.geometricTangentEquiv F (v + w)).val =
      (C.geometricTangentEquiv F v).val * (C.geometricTangentEquiv F w).val := by
  let : IsIntegral (X ⊗ X).left := AlgebraicGeometry.Albanese.Construction.Smooth.smooth_tensor_integral X X
  let : Smooth (X ⊗ X).hom := by dsimp; infer_instance
  let : IsMonHom (1 : X ⟶ X) := by
    change IsMonHom (toUnit X ≫ η[X])
    infer_instance
  let D := Intrinsic.TangentCharts.nativeTangentChart (X ⊗ X) 1
  let i₁ : X ⟶ X ⊗ X := lift (𝟙 X) (1 : X ⟶ X)
  let i₂ : X ⟶ X ⊗ X := lift (1 : X ⟶ X) (𝟙 X)
  let t := TangentAddition.geometricGroupDerivative F i₁ v + TangentAddition.geometricGroupDerivative F i₂ w
  have hp : TangentAddition.geometricGroupDerivative F (fst X X) t = v := by
    simp only [t, map_add, TangentAddition.geometricGroupDerivative_comp_apply, i₁, i₂,
      lift_fst, TangentAddition.geometricGroupDerivative_id, TangentAddition.geometricGroupDerivative_one, add_zero]
  have hq : TangentAddition.geometricGroupDerivative F (snd X X) t = w := by
    simp only [t, map_add, TangentAddition.geometricGroupDerivative_comp_apply, i₁, i₂,
      lift_snd, TangentAddition.geometricGroupDerivative_id, TangentAddition.geometricGroupDerivative_one, zero_add]
  have him : i₁ ≫ μ[X] = 𝟙 X := (Hom.mul_def _ _).symm.trans (mul_one _)
  have hjm : i₂ ≫ μ[X] = 𝟙 X := (Hom.mul_def _ _).symm.trans (one_mul _)
  have hm : TangentAddition.geometricGroupDerivative F μ[X] t = v + w := by
    simp only [t, map_add, TangentAddition.geometricGroupDerivative_comp_apply, him, hjm, TangentAddition.geometricGroupDerivative_id]
  have hp' : (D.geometricTangentEquiv F t).val ≫ fst X X = (C.geometricTangentEquiv F v).val :=
    (D.geometricGroup_naturality F C (fst X X) t).symm.trans
      (congrArg (fun u => (C.geometricTangentEquiv F u).val) hp)
  have hq' : (D.geometricTangentEquiv F t).val ≫ snd X X = (C.geometricTangentEquiv F w).val :=
    (D.geometricGroup_naturality F C (snd X X) t).symm.trans
      (congrArg (fun u => (C.geometricTangentEquiv F u).val) hq)
  have ht : (D.geometricTangentEquiv F t).val =
      lift (C.geometricTangentEquiv F v).val (C.geometricTangentEquiv F w).val := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hp'.trans (lift_fst _ _).symm
    · exact hq'.trans (lift_snd _ _).symm
  exact (congrArg (fun u => (C.geometricTangentEquiv F u).val) hm).symm.trans
    ((D.geometricGroup_naturality F C μ[X] t).trans
      ((congrArg (fun z : LieFieldTests.extendedDualTest ℂ F ⟶ X ⊗ X => z ≫ μ[X]) ht).trans
        (Hom.mul_def _ _).symm))

end

end OAI.RepresentationTheory.Theta.Geometric
