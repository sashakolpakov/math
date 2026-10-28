import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector

/-! # Coordinate Section Maps -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.CoordinateSectionMaps.Constructions

noncomputable section

/-! The actual coordinate-difference section on the affine product
is the difference of the genuine pullbacks from its two factors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.StalkCoordinates OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.CoordinateMaps
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coordinateSection_naturality (R S : CommRingCat) (X Y : Scheme)
    (e : X ≅ Spec R) (e' : Y ≅ Spec S) (f : X ⟶ Y) (g : S ⟶ R)
    (h : f ≫ e'.hom = e.hom ≫ Spec.map g) (s : S) :
    f.appTop (ProductIs.Constructions.StalkCoordinates.coordinateSection S Y e' s) = ProductIs.Constructions.StalkCoordinates.coordinateSection R X e (g s) := by
  have hm := congrArg (fun k : X ⟶ Spec S => k.appTop) h
  simp only [Scheme.Hom.comp_appTop] at hm
  have hv := ConcreteCategory.congr_hom hm ((Scheme.ΓSpecIso S).inv s)
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality g) s
  exact hv.trans (congrArg e.hom.appTop hn.symm)

theorem coordinateSection_isoSpec (X : Scheme) [IsAffine X] (r : Γ(X, ⊤)) :
    ProductIs.Constructions.StalkCoordinates.coordinateSection Γ(X, ⊤) X X.isoSpec r = r := by
  have he : X.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  unfold ProductIs.Constructions.StalkCoordinates.coordinateSection
  rw [he, Iso.inv_hom_id_apply]

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsAffine Y.left]

theorem coordinateSection_first (r : Γ(X.left, ⊤)) :
    ProductIs.Constructions.StalkCoordinates.coordinateSection (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤))) (pullback X.hom Y.hom)
      (ProductIs.Constructions.affineProductCoordinateIso X Y) (r ⊗ₜ[ℂ] 1) = (pullback.fst X.hom Y.hom).appTop r := by
  have h := coordinateSection_naturality (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)))
    Γ(X.left, ⊤) (pullback X.hom Y.hom) X.left (ProductIs.Constructions.affineProductCoordinateIso X Y) X.left.isoSpec
    (pullback.fst X.hom Y.hom) (CommRingCat.ofHom (algebraMap Γ(X.left, ⊤) (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤))))
    (ProductIs.Constructions.CoordinateMaps.coordinateIso_first X Y).symm r
  rw [coordinateSection_isoSpec] at h
  exact h.symm

theorem coordinateSection_second (r : Γ(Y.left, ⊤)) :
    ProductIs.Constructions.StalkCoordinates.coordinateSection (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤))) (pullback X.hom Y.hom)
      (ProductIs.Constructions.affineProductCoordinateIso X Y) (1 ⊗ₜ[ℂ] r) = (pullback.snd X.hom Y.hom).appTop r := by
  have h := coordinateSection_naturality (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)))
    Γ(Y.left, ⊤) (pullback X.hom Y.hom) Y.left (ProductIs.Constructions.affineProductCoordinateIso X Y) Y.left.isoSpec
    (pullback.snd X.hom Y.hom) (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)).toRingHom)
    (ProductIs.Constructions.CoordinateMaps.coordinateIso_second X Y).symm r
  rw [coordinateSection_isoSpec] at h
  exact h.symm

omit [IsAffine Y.left] in
theorem coordinateDifferenceSection_eq (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] (i : Fin n) :
    DiagonalEquations.Constructions.coordinateDifferenceSection X n i =
      (pullback.fst X.hom X.hom).appTop (EtaleSectionVector.Constructions.coordinateSections X n i) -
        (pullback.snd X.hom X.hom).appTop (EtaleSectionVector.Constructions.coordinateSections X n i) := by
  change ProductIs.Constructions.StalkCoordinates.coordinateSection _ _ _ (_ ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] _) = _
  have hs (a b : Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)) :
      ProductIs.Constructions.StalkCoordinates.coordinateSection _ _ (ProductIs.Constructions.affineProductCoordinateIso X X) (a - b) =
        ProductIs.Constructions.StalkCoordinates.coordinateSection _ _ (ProductIs.Constructions.affineProductCoordinateIso X X) a -
          ProductIs.Constructions.StalkCoordinates.coordinateSection _ _ (ProductIs.Constructions.affineProductCoordinateIso X X) b := by
    simp only [ProductIs.Constructions.StalkCoordinates.coordinateSection, map_sub]
  rw [hs, coordinateSection_first, coordinateSection_second]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.CoordinateSectionMaps.Constructions
