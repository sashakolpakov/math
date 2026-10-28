import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BaseChange
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Functor -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor.Construction

noncomputable section

/-! Functorial affine blowups with specified target ideals, for gluing in Blowups. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Coefficient extension with its target ideal specified separately. -/
def reesRingMapTo (I : Ideal R) (J : Ideal S) (φ : R →+* S) (h : I.map φ = J) :
    reesAlgebra I →+* reesAlgebra J where
  toFun p := ⟨p.val.map φ, by
    intro n
    rw [Polynomial.coeff_map, ← h, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem φ (p.property n)⟩
  map_one' := Subtype.ext (Polynomial.map_one φ)
  map_zero' := Subtype.ext (Polynomial.map_zero φ)
  map_add' _ _ := Subtype.ext (Polynomial.map_add φ)
  map_mul' _ _ := Subtype.ext (Polynomial.map_mul φ)

/-- The grading-preserving extension map for specified ideals. -/
def reesGradedMapTo (I : Ideal R) (J : Ideal S) (φ : R →+* S) (h : I.map φ = J) :
    ReesGrading.Construction.reesGrade I →+*ᵍ ReesGrading.Construction.reesGrade J where
  __ := reesRingMapTo I J φ h
  map_mem := by
    intro n p hp m hm
    change (p.val.map φ).coeff m = 0
    rw [Polynomial.coeff_map, hp m hm, map_zero]

theorem reesGradedMapTo_irrelevant_le
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) (h : I.map φ = J) :
    HomogeneousIdeal.irrelevant (ReesGrading.Construction.reesGrade J) ≤
      (HomogeneousIdeal.irrelevant (ReesGrading.Construction.reesGrade I)).map (reesGradedMapTo I J φ h) := by
  subst J
  exact ReesMap.Construction.reesGradedMap_irrelevant_le I φ

/-- The affine blowup map for an equality of extended center ideals. -/
def affineBlowupMapTo (I : Ideal R) (J : Ideal S) (φ : R →+* S) (h : I.map φ = J) :
    ReesGrading.Construction.affineBlowup J ⟶ ReesGrading.Construction.affineBlowup I :=
  Proj.map (reesGradedMapTo I J φ h) (reesGradedMapTo_irrelevant_le I J φ h)

theorem affineBlowupMapTo_over
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) (h : I.map φ = J) :
    affineBlowupMapTo I J φ h ≫ ReesGrading.Construction.affineBlowupToSpec I =
      ReesGrading.Construction.affineBlowupToSpec J ≫ Spec.map (CommRingCat.ofHom φ) := by
  subst J
  exact BaseOpen.Construction.affineBlowupMap_over I φ

@[simp]
theorem reesGradedMapTo_id (I : Ideal R) (h : I.map (RingHom.id R) = I) :
    reesGradedMapTo I I (RingHom.id R) h = GradedRingHom.id (ReesGrading.Construction.reesGrade I) := by
  ext p : 1
  apply Subtype.ext
  exact Polynomial.map_id

theorem reesGradedMapTo_comp
    (I : Ideal R) (J : Ideal S) (K : Ideal T) (φ : R →+* S) (ψ : S →+* T)
    (hφ : I.map φ = J) (hψ : J.map ψ = K) (hψφ : I.map (ψ.comp φ) = K) :
    reesGradedMapTo I K (ψ.comp φ) hψφ =
      (reesGradedMapTo J K ψ hψ).comp (reesGradedMapTo I J φ hφ) := by
  ext p : 1
  apply Subtype.ext
  exact (Polynomial.map_map φ ψ p.val).symm

@[simp]
theorem affineBlowupMapTo_id (I : Ideal R) (h : I.map (RingHom.id R) = I) :
    affineBlowupMapTo I I (RingHom.id R) h = 𝟙 (ReesGrading.Construction.affineBlowup I) := by
  unfold affineBlowupMapTo
  simp only [reesGradedMapTo_id, Proj.map_id]

theorem affineBlowupMapTo_comp
    (I : Ideal R) (J : Ideal S) (K : Ideal T) (φ : R →+* S) (ψ : S →+* T)
    (hφ : I.map φ = J) (hψ : J.map ψ = K) (hψφ : I.map (ψ.comp φ) = K) :
    affineBlowupMapTo I K (ψ.comp φ) hψφ =
      affineBlowupMapTo J K ψ hψ ≫ affineBlowupMapTo I J φ hφ := by
  unfold affineBlowupMapTo
  simpa only [← reesGradedMapTo_comp I J K φ ψ hφ hψ hψφ] using
    Proj.map_comp (reesGradedMapTo I J φ hφ) (reesGradedMapTo J K ψ hψ)
      (reesGradedMapTo_irrelevant_le I J φ hφ) (reesGradedMapTo_irrelevant_le J K ψ hψ)

variable {X : Scheme.{u}}

/-- Restriction of functions between two affine opens in a scheme. -/
abbrev affineRestriction {U V : X.affineOpens} (h : U ≤ V) : Γ(X, V) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom

@[simp]
theorem affineRestriction_refl (U : X.affineOpens) :
    affineRestriction (le_refl U) = RingHom.id Γ(X, U) := by
  simp [affineRestriction]

theorem affineRestriction_trans {U V W : X.affineOpens} (hUV : U ≤ V) (hVW : V ≤ W) :
    affineRestriction (hUV.trans hVW) =
      (affineRestriction hUV).comp (affineRestriction hVW) := by
  change (X.presheaf.map ((homOfLE (X := X.Opens) hUV) ≫ homOfLE hVW).op).hom = _
  rw [op_comp, Functor.map_comp, CommRingCat.hom_comp]

/-- The ideal sheaf compatibility law expressed through affine restriction. -/
theorem affineRestriction_ideal (I : X.IdealSheafData) {U V : X.affineOpens} (h : U ≤ V) :
    (I.ideal V).map (affineRestriction h) = I.ideal U :=
  I.map_ideal h

/-- Blowups of the affine pieces of an ideal sheaf and their restriction maps. -/
def idealBlowupFunctor (I : X.IdealSheafData) : X.affineOpens ⥤ Scheme.{u} where
  obj U := ReesGrading.Construction.affineBlowup (I.ideal U)
  map {U V} h := affineBlowupMapTo (I.ideal V) (I.ideal U)
    (affineRestriction (leOfHom h)) (affineRestriction_ideal I _)
  map_id U := by
    simp only [affineRestriction_refl, affineBlowupMapTo_id]
  map_comp {U V W} hUV hVW := by
    simpa only [← affineRestriction_trans] using
      affineBlowupMapTo_comp (I.ideal W) (I.ideal V) (I.ideal U)
        (affineRestriction (leOfHom hVW)) (affineRestriction (leOfHom hUV))
        (affineRestriction_ideal I _) (affineRestriction_ideal I _) (by
          rw [← affineRestriction_trans]
          exact affineRestriction_ideal I _)

/-- Restriction of affine coordinate rings represents the inclusion of opens. -/
theorem affineRestriction_over {U V : X.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (affineRestriction h)) ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ X.homOfLE h := by
  apply (cancel_mono V.1.ι).mp
  change Spec.map (X.presheaf.map (homOfLE (X := X.Opens) h).op) ≫
    V.2.isoSpec.inv ≫ V.1.ι = _
  change Spec.map (X.presheaf.map (homOfLE (X := X.Opens) h).op) ≫ V.2.fromSpec = _
  rw [IsAffineOpen.map_fromSpec V.2 U.2]
  simp only [Category.assoc, Scheme.homOfLE_ι]
  rfl

/-- The structure maps on affine blowups form a natural map to the affine cover. -/
def idealBlowupNatTrans (I : X.IdealSheafData) :
    idealBlowupFunctor I ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app U := ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.isoSpec.inv
  naturality {U V} h := by
    change affineBlowupMapTo (I.ideal V) (I.ideal U)
        (affineRestriction (leOfHom h)) (affineRestriction_ideal I _) ≫
        (ReesGrading.Construction.affineBlowupToSpec (I.ideal V) ≫ V.2.isoSpec.inv) =
      (ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.isoSpec.inv) ≫ X.homOfLE (leOfHom h)
    rw [← Category.assoc, affineBlowupMapTo_over, Category.assoc, affineRestriction_over,
      Category.assoc]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor.Construction
