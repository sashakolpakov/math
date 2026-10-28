import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSections
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Chart Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartRefinement

noncomputable section

/-! An open affine refinement of a spectrum chart gives an actual affine
subopen of the original scheme, with its section ring and ideals identified. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]

abbrev map : Spec (CommRingCat.of S) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec

abbrev openSet : X.Opens := ChartRefinement.map U hU φ ''ᵁ ⊤

theorem affine : IsAffineOpen (openSet U hU φ) :=
  (isAffineOpen_top (Spec (CommRingCat.of S))).image_of_isOpenImmersion (ChartRefinement.map U hU φ)

theorem le : openSet U hU φ ≤ U := by
  rintro x ⟨z, _, rfl⟩
  change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ)) z) ∈ U
  have h : hU.fromSpec ((Spec.map (CommRingCat.ofHom φ)) z) ∈ hU.fromSpec.opensRange := ⟨_, rfl⟩
  simpa only [hU.opensRange_fromSpec] using h

def sectionsIso : Γ(X, openSet U hU φ) ≅ CommRingCat.of S :=
  (ChartRefinement.map U hU φ).appIso ⊤ ≪≫ Scheme.ΓSpecIso (CommRingCat.of S)

theorem restriction :
    X.presheaf.map (homOfLE (le U hU φ)).op ≫ (sectionsIso U hU φ).hom =
      CommRingCat.ofHom φ := by
  change X.presheaf.map (homOfLE (le U hU φ)).op ≫
    ((ChartRefinement.map U hU φ).appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom = _
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE_assoc]
  rw [show (ChartRefinement.map U hU φ).appLE U ⊤ _ =
    hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge ≫
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top from
        (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm]
  rw [ChartSections.fromSpec_appLE]
  change (Scheme.ΓSpecIso Γ(X, U)).inv ≫
    ((Spec.map (CommRingCat.ofHom φ)).appTop ≫
      (Spec (CommRingCat.of S)).presheaf.map (𝟙 (op ⊤))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of S)).hom = _
  rw [(Spec (CommRingCat.of S)).presheaf.map_id, Category.comp_id]
  rw [Scheme.ΓSpecIso_naturality]
  exact (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id_assoc (CommRingCat.ofHom φ)

theorem ideal (I : X.IdealSheafData) :
    (I.ideal ⟨openSet U hU φ, affine U hU φ⟩).map (sectionsIso U hU φ).hom.hom =
      (I.ideal ⟨U, hU⟩).map φ := by
  rw [← I.map_ideal (U := ⟨openSet U hU φ, affine U hU φ⟩) (V := ⟨U, hU⟩) (le U hU φ),
    Ideal.map_map]
  change (I.ideal ⟨U, hU⟩).map
    (X.presheaf.map (homOfLE (le U hU φ)).op ≫ (sectionsIso U hU φ).hom).hom = _
  rw [restriction]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartRefinement
