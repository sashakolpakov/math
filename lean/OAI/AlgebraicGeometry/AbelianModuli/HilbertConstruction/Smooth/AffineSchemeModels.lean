import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModelsAbove
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverChartPoints

/-! # Affine Scheme Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels

noncomputable section

/-! Smooth affine schemes over an arbitrary ring descend with an actual Cartesian recovery map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R))) [IsAffine X.left]

theorem affineOverAlgebra_smooth [Smooth X.hom] : Algebra.Smooth R (Affine.OverChartPoints.affineOverAlgebra R X) := by
  let e := Affine.OverChartPoints.affineOverIso R X
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have hs : Smooth (e.inv.left ≫ X.hom) := inferInstance
  have he : e.inv.left ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (Affine.OverChartPoints.affineOverAlgebra R X))) := e.inv.w
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Affine.OverChartPoints.affineOverAlgebra R X)))) :=
    (congrArg Smooth he).mp hs
  exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)

def affineSchemeModelMap (M : AffineModels.SmoothAffineModel R (Affine.OverChartPoints.affineOverAlgebra R X)) :
    X.left ⟶ Spec (.of M.algebra) := (Affine.OverChartPoints.affineOverIso R X).hom.left ≫ M.map

theorem affineSchemeModel_isPullback (M : AffineModels.SmoothAffineModel R (Affine.OverChartPoints.affineOverAlgebra R X)) :
    IsPullback (affineSchemeModelMap R X M) X.hom M.structureMap
      (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)) := by
  let e := Affine.OverChartPoints.affineOverIso R X
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have H : IsPullback e.hom.left X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R (Affine.OverChartPoints.affineOverAlgebra R X))))
      (𝟙 (Spec (.of R))) :=
    IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩
  have h := H.paste_horiz M.isPullback
  exact (congrArg (fun a => IsPullback (affineSchemeModelMap R X M) X.hom M.structureMap a)
    (Category.id_comp _)).mp h

theorem exists_smoothAffineSchemeModel_above [Smooth X.hom]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ M : AffineModels.SmoothAffineModel R (Affine.OverChartPoints.affineOverAlgebra R X), C ≤ M.coefficients ∧
      ∃ q : X.left ⟶ Spec (.of M.algebra), IsPullback q X.hom M.structureMap
        (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)) := by
  have := affineOverAlgebra_smooth R X
  obtain ⟨M, hM⟩ := AffineModelsAbove.exists_smoothAffineModel_above R (Affine.OverChartPoints.affineOverAlgebra R X) C
  exact ⟨M, hM, affineSchemeModelMap R X M, affineSchemeModel_isPullback R X M⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels
