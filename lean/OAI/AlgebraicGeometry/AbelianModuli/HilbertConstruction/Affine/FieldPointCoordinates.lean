import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverChartPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoMorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Field Point Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FieldPointCoordinates

noncomputable section

/-! Actual rational points and finite ranks of affine schemes over a field are the algebra homomorphisms and dimension of their canonical coordinate algebra. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

def algebraSelfSpecIso (K : Type u) [CommRing K] :
    Over.mk (𝟙 (Spec (.of K))) ≅ (algSpec (.of K)).obj (op (CommAlgCat.of K K)) := by
  refine Over.isoMk (Iso.refl _) ?_
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
  simp

def affineFieldPointCoordinates (K : Type u) [Field K]
    (M : Over (Spec (.of K))) [IsAffine M.left] :
    (Over.mk (𝟙 (Spec (.of K))) ⟶ M) ≃ (OverChartPoints.affineOverAlgebra K M →ₐ[K] K) :=
  ((algebraSelfSpecIso K).homCongr (OverChartPoints.affineOverIso K M)).trans
    (((algSpec.fullyFaithful (R := CommRingCat.of K)).homEquiv.symm.trans (opEquiv _ _)).trans
      { toFun := fun f => f.hom
        invFun := CommAlgCat.ofHom
        left_inv := CommAlgCat.ofHom_hom
        right_inv := CommAlgCat.hom_ofHom })

theorem finiteAffineField_coordinateAlgebra_finite (K : Type u) [Field K]
    (M : Over (Spec (.of K))) [IsAffine M.left] [IsFinite M.hom] :
    Module.Finite K (OverChartPoints.affineOverAlgebra K M) := by
  have hF : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (OverChartPoints.affineOverAlgebra K M)))) :=
    (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@IsFinite) (OverChartPoints.affineOverIso K M)).mp inferInstance
  exact (IsFinite.SpecMap_iff _).mp hF

theorem finiteAffineField_finrank (K : Type u) [Field K]
    (M : Over (Spec (.of K))) [IsAffine M.left] [IsFinite M.hom] (x : Spec (.of K)) :
    M.hom.finrank x = Module.finrank K (OverChartPoints.affineOverAlgebra K M) := by
  let B := OverChartPoints.affineOverAlgebra K M
  have : Module.Finite K B := finiteAffineField_coordinateAlgebra_finite K M
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap K B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hfinite : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K B))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let e := OverChartPoints.affineOverIso K M
  have hiso : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hc := congrFun (@Scheme.Hom.finrank_comp_left_of_isIso (X := M.left) (Y := Spec (.of B)) (S := Spec (.of K))
    e.hom.left (Spec.map (CommRingCat.ofHom (algebraMap K B))) hiso hflat hfinite) x
  have he : M.hom.finrank x = (Spec.map (CommRingCat.ofHom (algebraMap K B))).finrank x :=
    (congrArg (fun f : M.left ⟶ Spec (.of K) => f.finrank x) e.hom.w.symm).trans hc
  have hr : Module.rankAtStalk (R := K) B x = Module.finrank K B := by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl
  exact he.trans ((Scheme.Hom.finrank_SpecMap_algebraMap K B x).trans hr)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FieldPointCoordinates
