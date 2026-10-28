import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Chart Properties -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties.BundleCycles

noncomputable section

/-! # LineBundleCycles: geometric properties proved from actual affine-space pullback charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSpaceSpecProjection_smooth (B : CommRingCat.{0}) (ι : Type) [Finite ι] :
    Smooth (AffineSpace ι (Spec B) ↘ Spec B) := by
  let e := AffineSpace.SpecIso ι B
  let q := Spec.map (CommRingCat.ofHom (MvPolynomial.C : B →+* MvPolynomial ι B))
  have hq : Smooth q := HasRingHomProperty.Spec_iff.mpr
    (RingHom.smooth_algebraMap.mpr (Algebra.Smooth.mk inferInstance inferInstance))
  have he : AffineSpace ι (Spec B) ↘ Spec B = e.hom ≫ q := by
    apply (cancel_epi e.inv).mp
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    exact AffineSpace.SpecIso_inv_over (n := ι) B
  have h : Smooth (e.hom ≫ q) := @smooth_comp _ _ e.hom _ q inferInstance hq
  exact he.symm ▸ h

theorem morphismProperty_of_affineSpaceCharts (P : MorphismProperty Scheme.{0})
    [IsZariskiLocalAtTarget P] {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hcharts : ∀ y : Y, ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ Y) (ι : Type) (_ : Finite ι)
      (j : AffineSpace ι (Spec B) ⟶ X),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ y ∈ Set.range i ∧
      IsPullback (AffineSpace ι (Spec B) ↘ Spec B) j i f)
    (hP : ∀ (B : CommRingCat.{0}) (ι : Type) [Finite ι], P (AffineSpace ι (Spec B) ↘ Spec B)) : P f := by
  choose B i ι hι j hi hj hy hsq using hcharts
  let C : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec (B y)) i
    (fun y => ⟨y, hy y⟩) hi
  exact Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks P f C
    (fun y => AffineSpace (ι y) (Spec (B y))) j
    (fun y => AffineSpace (ι y) (Spec (B y)) ↘ Spec (B y)) hsq
    (fun y => @hP (B y) (ι y) (hι y))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties.BundleCycles
