import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ComparisonTensorIso

/-! # Tensor Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorProjection

noncomputable section

/-! The coordinate tensor algebra realizes the actual base change of any affine scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u

variable (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
variable (X : Over (Spec (.of C))) [IsAffine X.left]

def affineTensorProjection : Spec (.of (R ⊗[C] OverChartPoints.affineOverAlgebra C X)) ⟶ X.left :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
    (R := C) (A := R) (B := OverChartPoints.affineOverAlgebra C X)).toRingHom) ≫ (OverChartPoints.affineOverIso C X).inv.left

theorem affineTensorProjection_isPullback :
    IsPullback (affineTensorProjection C R X)
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[C] OverChartPoints.affineOverAlgebra C X))))
      X.hom (Spec.map (CommRingCat.ofHom (algebraMap C R))) := by
  let e := OverChartPoints.affineOverIso C X
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have he : IsPullback e.inv.left
      (Spec.map (CommRingCat.ofHom (algebraMap C (OverChartPoints.affineOverAlgebra C X)))) X.hom
      (𝟙 (Spec (.of C))) :=
    IsPullback.of_horiz_isIso ⟨e.inv.w.trans (Category.comp_id _).symm⟩
  have h := (Tensor.ComparisonIso.naturalTensorProjection_isPullback
    (C := C) (R := R) (A := OverChartPoints.affineOverAlgebra C X)).paste_horiz he
  exact (congrArg (fun b => IsPullback (affineTensorProjection C R X)
    (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[C] OverChartPoints.affineOverAlgebra C X)))) X.hom b)
    (Category.comp_id _)).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorProjection
