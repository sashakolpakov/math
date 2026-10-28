import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ImageFunctions
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Cover Coefficient Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCoefficientDetection

noncomputable section

/-! An affine open cover of a spectrum jointly detects zero in the coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem globalSections_eq_of_open_cover {X : Scheme.{u}} (C : Scheme.OpenCover.{v} X)
    (a b : Γ(X, ⊤)) (h : ∀ i, (C.f i).appTop a = (C.f i).appTop b) : a = b := by
  let U := fun i => C.f i ''ᵁ ⊤
  have hU : (⨆ i, U i) = ⊤ := by
    simpa only [U, Scheme.Hom.image_top_eq_opensRange] using C.iSup_opensRange
  apply X.sheaf.eq_of_locally_eq' U ⊤ (fun i => (U i).leTop) hU.ge
  intro i
  exact (Open.ImageFunctions.imageFunction_appTop (C.f i) a).symm.trans
    ((congrArg (fun t => ((C.f i).appIso ⊤).inv t) (h i)).trans
      (Open.ImageFunctions.imageFunction_appTop (C.f i) b))

variable (R : CommRingCat.{u}) (C : Scheme.AffineOpenCover.{v} (Spec R))

def affineCoverCoefficientMap (i : C.I₀) : R →+* C.X i :=
  (Spec.fullyFaithful.preimage (C.f i)).unop.hom

theorem affineCoverCoefficientMap_spec (i : C.I₀) :
    Spec.map (CommRingCat.ofHom (affineCoverCoefficientMap R C i)) = C.f i :=
  Spec.fullyFaithful.map_preimage (C.f i)

theorem affineCoverCoefficientMap_sections (i : C.I₀) (r : R) :
    (C.f i).appTop ((Scheme.ΓSpecIso R).inv r) =
      (Scheme.ΓSpecIso (C.X i)).inv (affineCoverCoefficientMap R C i r) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (affineCoverCoefficientMap R C i))
  rw [affineCoverCoefficientMap_spec] at h
  exact (ConcreteCategory.congr_hom h r).symm

theorem affineCoverCoefficientMap_detect_zero (r : R)
    (h : ∀ i, affineCoverCoefficientMap R C i r = 0) : r = 0 := by
  have hr : (Scheme.ΓSpecIso R).inv r = 0 := by
    apply globalSections_eq_of_open_cover C.openCover
    intro i
    change C.I₀ at i
    rw [map_zero]
    change (C.f i).appTop ((Scheme.ΓSpecIso R).inv r) = 0
    rw [affineCoverCoefficientMap_sections, h i, map_zero]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1
    (hr.trans (map_zero (Scheme.ΓSpecIso R).inv.hom).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCoefficientDetection
