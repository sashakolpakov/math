import OAI.NumberTheory.PadicHodge.IntegralComparison.PairedOpenSectionEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase

/-! # Equiv Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivGeometry

noncomputable section

/-! Realize a specified affine section-algebra equivalence by two
open embeddings of its original affine spectrum. Smaller neighborhoods
are transported through that same equivalence. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X₁ X₂ : Over (Spec (CommRingCat.of R)))
  (U₁ : X₁.left.Opens) (U₂ : X₂.left.Opens)
  (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)

abbrev ring (X : Over (Spec (CommRingCat.of R))) (U : X.left.Opens) :=
  (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U)

def common : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (ring R X₁ U₁))))

def left : (common R X₁ U₁).left ⟶ X₁.left := hU₁.fromSpec

variable (e : ring R X₁ U₁ ≃ₐ[R] ring R X₂ U₂)

def right : (common R X₁ U₁).left ⟶ X₂.left :=
  Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ hU₂.fromSpec

instance left_open : IsOpenImmersion (EquivGeometry.left R X₁ U₁ hU₁) := by
  dsimp only [EquivGeometry.left]
  infer_instance

instance right_open : IsOpenImmersion (right R X₁ X₂ U₁ U₂ hU₂ e) := by
  let : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) :=
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).isIso_inv
  dsimp only [right]
  infer_instance

theorem left_over : EquivGeometry.left R X₁ U₁ hU₁ ≫ X₁.hom = (common R X₁ U₁).hom :=
  AffineOpen.SectionBase.overBase R X₁ U₁ hU₁

theorem right_over : right R X₁ X₂ U₁ U₂ hU₂ e ≫ X₂.hom = (common R X₁ U₁).hom := by
  rw [right, Category.assoc, AffineOpen.SectionBase.overBase, ← Spec.map_comp]
  congr 1
  ext r
  exact e.symm.commutes r

theorem left_range : (EquivGeometry.left R X₁ U₁ hU₁).opensRange = U₁ := hU₁.opensRange_fromSpec

theorem right_range : (right R X₁ X₂ U₁ U₂ hU₂ e).opensRange = U₂ := by
  let : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) :=
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).isIso_inv
  exact (Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (show Γ(X₂.left,U₂) ⟶ Γ(X₁.left,U₁) from CommRingCat.ofHom e.symm.toRingHom))
    hU₂.fromSpec).trans hU₂.opensRange_fromSpec

variable (V : X₁.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U₁)

def sourceOpen : (common R X₁ U₁).left.Opens := (EquivGeometry.left R X₁ U₁ hU₁) ⁻¹ᵁ V

def targetOpen : X₂.left.Opens :=
  (right R X₁ X₂ U₁ U₂ hU₂ e) ''ᵁ sourceOpen R X₁ U₁ hU₁ V

include hV hVU in
theorem source_affine : IsAffineOpen (sourceOpen R X₁ U₁ hU₁ V) :=
  hV.preimage_of_isOpenImmersion (EquivGeometry.left R X₁ U₁ hU₁) ((left_range R X₁ U₁ hU₁).symm ▸ hVU)

include hV hVU in
theorem target_affine : IsAffineOpen (targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V) :=
  (source_affine R X₁ U₁ hU₁ V hV hVU).image_of_isOpenImmersion
    (right R X₁ X₂ U₁ U₂ hU₂ e)

include hVU in
theorem source_image : (EquivGeometry.left R X₁ U₁ hU₁) ''ᵁ sourceOpen R X₁ U₁ hU₁ V = V := by
  rw [sourceOpen, Scheme.Hom.image_preimage_eq_opensRange_inf, left_range, inf_eq_right.mpr hVU]

theorem target_below : targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V ≤ U₂ := by
  exact (show targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V ≤
    (right R X₁ X₂ U₁ U₂ hU₂ e).opensRange from Set.image_subset_range _ _).trans
      (right_range R X₁ X₂ U₁ U₂ hU₂ e).le

def sectionIso : (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₁).obj (op V) ≅
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₂).obj
      (op (targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V)) :=
  (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₁).mapIso
      (eqToIso (source_image R X₁ U₁ hU₁ V hVU)).op ≪≫
    PairedOpenSectionEquiv.iso R (common R X₁ U₁) X₁ X₂
      (EquivGeometry.left R X₁ U₁ hU₁) (right R X₁ X₂ U₁ U₂ hU₂ e)
      (left_over R X₁ U₁ hU₁) (right_over R X₁ X₂ U₁ U₂ hU₂ e)
      (sourceOpen R X₁ U₁ hU₁ V)

def sectionEquiv : ring R X₁ V ≃ₐ[R]
    ring R X₂ (targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V) :=
  CommAlgCat.algEquivOfIso (sectionIso R X₁ X₂ U₁ U₂ hU₁ hU₂ e V hVU)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivGeometry
