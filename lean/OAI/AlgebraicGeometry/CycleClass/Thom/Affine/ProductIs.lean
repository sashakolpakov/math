import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Product Is -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions

/-! Genuine affine scheme products over the complex base are spectra of
the actual tensor product of their global-section algebras. Reducedness
and integrality follow from the proved algebraic tensor-product results. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain.Constructions.Reduced

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsAffine Y.left]

def affineProductCoordinateIso : pullback X.hom Y.hom ≅
    Spec (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤))) := by
  let f := pullback.map X.hom Y.hom
    (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ Γ(X.left, ⊤)).hom (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ Γ(Y.left, ⊤)).hom
    (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.left (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).hom.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    (by simpa only [Category.comp_id] using (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.w.symm)
    (by simpa only [Category.comp_id] using (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).hom.w.symm)
  have : IsIso f := by dsimp only [f]; infer_instance
  exact asIso f ≪≫ pullbackSpecIso ℂ Γ(X.left, ⊤) Γ(Y.left, ⊤)

theorem affineProduct_isReduced [LocallyOfFiniteType X.hom]
    [AlgebraicGeometry.IsReduced X.left] [AlgebraicGeometry.IsReduced Y.left] :
    AlgebraicGeometry.IsReduced (pullback X.hom Y.hom) := by
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  let : _root_.IsReduced (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)) := Tensor.ProductDomain.Constructions.Reduced.tensorProduct_isReduced
  exact isReduced_of_isOpenImmersion (affineProductCoordinateIso X Y).hom

theorem affineProduct_isIntegral [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsIntegral Y.left] : IsIntegral (pullback X.hom Y.hom) := by
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  let : IsDomain (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)) := Tensor.ProductDomain.Constructions.tensorProduct_isDomain
  exact IsIntegral.of_isIso (affineProductCoordinateIso X Y).inv

end AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.CoordinateMaps

/-! The affine product coordinate isomorphism preserves both genuine
projections and identifies the actual geometric diagonal with the
multiplication map of the tensor-product algebra. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsAffine Y.left]

omit [IsAffine Y.left] in
def affineCoordinateMap : X.left ⟶ Spec (CommRingCat.of Γ(X.left, ⊤)) :=
  (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.left

@[reassoc]
theorem coordinateIso_first :
    (affineProductCoordinateIso X Y).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X.left, ⊤) (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)))) =
        pullback.fst X.hom Y.hom ≫ affineCoordinateMap X := by
  unfold affineProductCoordinateIso
  dsimp only [Iso.trans_hom, asIso_hom]
  rw [Category.assoc, pullbackSpecIso_hom_fst']
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem coordinateIso_second :
    (affineProductCoordinateIso X Y).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)).toRingHom) =
        pullback.snd X.hom Y.hom ≫ affineCoordinateMap Y := by
  simp only [AlgHom.toRingHom_eq_coe]
  unfold affineProductCoordinateIso
  dsimp only [Iso.trans_hom, asIso_hom]
  rw [Category.assoc, pullbackSpecIso_hom_snd]
  exact pullback.lift_snd _ _ _

omit [IsAffine Y.left] in
theorem coordinateIso_diagonal :
    pullback.diagonal X.hom ≫ (affineProductCoordinateIso X X).hom =
      affineCoordinateMap X ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' ℂ :
          Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤)).toRingHom) := by
  let R := Γ(X.left, ⊤)
  let m := CommRingCat.ofHom (Algebra.TensorProduct.lmul' ℂ : R ⊗[ℂ] R →ₐ[ℂ] R).toRingHom
  have hl : CommRingCat.ofHom (algebraMap R (R ⊗[ℂ] R)) ≫ m = 𝟙 (CommRingCat.of R) := by
    ext r
    change Algebra.TensorProduct.lmul' ℂ (r ⊗ₜ[ℂ] 1) = r
    simp only [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
  have hr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[ℂ] R ⊗[ℂ] R).toRingHom ≫ m =
      𝟙 (CommRingCat.of R) := by
    ext r
    change Algebra.TensorProduct.lmul' ℂ (1 ⊗ₜ[ℂ] r) = r
    simp only [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
  apply (cancel_mono (pullbackSpecIso ℂ R R).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst']
    rw [coordinateIso_first, ← Category.assoc, pullback.diagonal_fst, Category.id_comp]
    rw [← Spec.map_comp, hl, Spec.map_id, Category.comp_id]
  · simp only [Category.assoc, pullbackSpecIso_inv_snd, ← AlgHom.toRingHom_eq_coe]
    rw [coordinateIso_second, ← Category.assoc, pullback.diagonal_snd, Category.id_comp]
    rw [← Spec.map_comp, hr, Spec.map_id, Category.comp_id]

end AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.CoordinateMaps

namespace AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.StalkCoordinates

/-! Actual stalk coordinates for a scheme isomorphic to an affine
spectrum. Global coordinate sections map to the native localization
elements, without an abstractly chosen stalk identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : CommRingCat) (X : Scheme) (e : X ≅ Spec R)

def coordinateSection (r : R) : Γ(X, ⊤) := e.hom.appTop ((Scheme.ΓSpecIso R).inv r)

def stalkCoordinateIso (x : X) : X.presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime (e.hom x).asIdeal) :=
  (asIso (e.hom.stalkMap x)).symm ≪≫ Spec.stalkIso R (e.hom x)

theorem coordinateSection_germ (x : X) (r : R) :
    (stalkCoordinateIso R X e x).hom (X.presheaf.germ ⊤ x trivial (coordinateSection R X e r)) =
      algebraMap R (Localization.AtPrime (e.hom x).asIdeal) r := by
  have hg : e.hom.stalkMap x
      ((Spec R).presheaf.germ ⊤ (e.hom x) trivial ((Scheme.ΓSpecIso R).inv r)) =
        X.presheaf.germ ⊤ x trivial (coordinateSection R X e r) :=
    e.hom.germ_stalkMap_apply ⊤ x trivial ((Scheme.ΓSpecIso R).inv r)
  rw [← hg]
  change (Spec.stalkIso R (e.hom x)).hom
    ((asIso (e.hom.stalkMap x)).inv (e.hom.stalkMap x
      ((Spec R).presheaf.germ ⊤ (e.hom x) trivial ((Scheme.ΓSpecIso R).inv r)))) = _
  have hc := (asIso (e.hom.stalkMap x)).hom_inv_id_apply
    ((Spec R).presheaf.germ ⊤ (e.hom x) trivial ((Scheme.ΓSpecIso R).inv r))
  apply (congrArg (Spec.stalkIso R (e.hom x)).hom hc).trans
  have hp := ConcreteCategory.congr_hom (Spec.germ_stalkMapIso_hom (R := R) (e.hom x)) ((Scheme.ΓSpecIso R).inv r)
  exact hp.trans (congrArg (algebraMap R (Localization.AtPrime (e.hom x).asIdeal))
    ((Scheme.ΓSpecIso R).inv_hom_id_apply r))

theorem coordinateSection_zero_iff (x : X) (r : R) :
    X.presheaf.germ ⊤ x trivial (coordinateSection R X e r) = 0 ↔
      algebraMap R (Localization.AtPrime (e.hom x).asIdeal) r = 0 := by
  rw [← coordinateSection_germ R X e x r]
  constructor
  · intro h
    exact (congrArg (stalkCoordinateIso R X e x).hom h).trans (map_zero _)
  · intro h
    apply (ConcreteCategory.bijective_of_isIso (stalkCoordinateIso R X e x).hom).1
    exact h.trans (map_zero (stalkCoordinateIso R X e x).hom.hom).symm

end AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.StalkCoordinates

end

end OAI
