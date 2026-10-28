import OAI.NumberTheory.PadicHodge.IntegralComparison.NonpositiveProjectiveResolution
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Nonpositive Cone Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NonpositiveConeExtension

noncomputable section

/-! Extension from nonnegative chain degrees to nonpositive cochain
degrees preserves the actual homotopy cofiber, including its inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

abbrev shape := NonpositiveProjectiveResolution.shape

theorem chain_predecessor (j : ℕ) : ∃ i, (ComplexShape.down ℕ).Rel i j := ⟨j + 1, rfl⟩

variable {F G : ChainComplex C ℕ} (φ : F ⟶ G)

abbrev extendedMap := extendMap φ shape

def inclusionHomotopy : Homotopy
    (extendedMap φ ≫ extendMap (homotopyCofiber.inr φ) shape) 0 where
  hom := ((homotopyCofiber.inrCompHomotopy φ chain_predecessor).extend shape).hom
  zero := ((homotopyCofiber.inrCompHomotopy φ chain_predecessor).extend shape).zero
  comm i := by
    simpa only [extendMap_comp, extendMap_zero] using
      ((homotopyCofiber.inrCompHomotopy φ chain_predecessor).extend shape).comm i

def comparison : homotopyCofiber (extendedMap φ) ⟶ (homotopyCofiber φ).extend shape :=
  homotopyCofiber.desc (extendedMap φ) (extendMap (homotopyCofiber.inr φ) shape)
    (inclusionHomotopy φ)

theorem inr_comparison : homotopyCofiber.inr (extendedMap φ) ≫ comparison φ =
    extendMap (homotopyCofiber.inr φ) shape :=
  homotopyCofiber.inr_desc _ _ _

theorem image_rel (n : ℕ) : (ComplexShape.up ℤ).Rel (shape.f (n + 1)) (shape.f n) := by
  change (0 - ((n + 1 : ℕ) : ℤ)) + 1 = 0 - (n : ℤ)
  omega

def imageIso (n : ℕ) :
    (homotopyCofiber (extendedMap φ)).X (shape.f (n + 1)) ≅
      ((homotopyCofiber φ).extend shape).X (shape.f (n + 1)) :=
  homotopyCofiber.XIsoBiprod (extendedMap φ) _ _ (image_rel n) ≪≫
    biprod.mapIso (F.extendXIso shape (i := n) rfl) (G.extendXIso shape (i := n + 1) rfl) ≪≫
      (homotopyCofiber.XIsoBiprod φ (n + 1) n rfl).symm ≪≫
        ((homotopyCofiber φ).extendXIso shape (i := n + 1) rfl).symm

theorem comparison_image (n : ℕ) : (comparison φ).f (shape.f (n + 1)) = (imageIso φ n).hom := by
  apply homotopyCofiber.ext_from_X (extendedMap φ) (shape.f n) (shape.f (n + 1)) (image_rel n)
  · rw [comparison, homotopyCofiber.inlX_desc_f]
    change ((homotopyCofiber.inrCompHomotopy φ chain_predecessor).extend shape).hom
      (shape.f n) (shape.f (n + 1)) = _
    rw [Homotopy.extend_hom_eq _ shape rfl rfl,
      homotopyCofiber.inrCompHomotopy_hom _ _ n (n + 1) rfl]
    simp only [imageIso, Iso.trans_hom, Iso.symm_hom,
      homotopyCofiber.inlX_XIsoBiprod_hom_assoc, biprod.mapIso_hom, biprod.inl_map_assoc,
      homotopyCofiber.inl_XIsoBiprod_inv_assoc]
  · rw [comparison, homotopyCofiber.inrX_desc_f]
    rw [extendMap_f _ shape rfl]
    simp only [imageIso, Iso.trans_hom, Iso.symm_hom,
      homotopyCofiber.inrX_XIsoBiprod_hom_assoc, biprod.mapIso_hom, biprod.inr_map_assoc,
      homotopyCofiber.inr_XIsoBiprod_inv_assoc, homotopyCofiber.inr_f]

theorem isZero_positive (K : ChainComplex C ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((K.extend shape).X i) :=
  K.isZero_extend_X shape i (by intro n; change 0 - (n : ℤ) ≠ i; omega)

theorem inr_isIso_of_zero_next {ι : Type*} {c : ComplexShape ι}
    [DecidableRel c.Rel] {A B : HomologicalComplex C c} (a : A ⟶ B) (i : ι)
    (hA : ∀ j, c.Rel i j → IsZero (A.X j)) : IsIso (homotopyCofiber.inrX a i) := by
  refine ⟨⟨homotopyCofiber.sndX a i, homotopyCofiber.inrX_sndX a i, ?_⟩⟩
  by_cases hi : c.Rel i (c.next i)
  · apply homotopyCofiber.ext_from_X a (c.next i) i hi
    · exact (hA (c.next i) hi).eq_of_src _ _
    · simp only [homotopyCofiber.inrX_sndX_assoc, Category.comp_id]
  · exact homotopyCofiber.sndX_inrX a i hi

theorem comparison_zero_isIso : IsIso ((comparison φ).f (shape.f 0)) := by
  have h0 : shape.f 0 = 0 := by simp [shape, NonpositiveProjectiveResolution.shape]
  let : IsIso (homotopyCofiber.inrX (extendedMap φ) (shape.f 0)) :=
    inr_isIso_of_zero_next (extendedMap φ) _ (by
      intro j hj
      exact isZero_positive F j (by change shape.f 0 + 1 = j at hj; omega))
  let : IsIso (homotopyCofiber.inrX φ 0) := inr_isIso_of_zero_next φ 0 (by
    intro j hj
    have h : j + 1 = 0 := hj
    omega)
  have hα : IsIso ((extendMap (homotopyCofiber.inr φ) shape).f (shape.f 0)) := by
    rw [extendMap_f _ shape rfl]
    change IsIso ((G.extendXIso shape (i := 0) rfl).hom ≫ homotopyCofiber.inrX φ 0 ≫
      ((homotopyCofiber φ).extendXIso shape (i := 0) rfl).inv)
    infer_instance
  have hc : homotopyCofiber.inrX (extendedMap φ) (shape.f 0) ≫ (comparison φ).f (shape.f 0) =
      (extendMap (homotopyCofiber.inr φ) shape).f (shape.f 0) :=
    homotopyCofiber.inrX_desc_f _ _ _ _
  have : IsIso (homotopyCofiber.inrX (extendedMap φ) (shape.f 0) ≫
      (comparison φ).f (shape.f 0)) := hc.symm ▸ hα
  exact IsIso.of_isIso_comp_left (homotopyCofiber.inrX (extendedMap φ) (shape.f 0)) _

theorem comparison_component_isIso (i : ℤ) : IsIso ((comparison φ).f i) := by
  by_cases hi : 0 < i
  · apply (homotopyCofiber.isZero_X (extendedMap φ) i (isZero_positive G i hi) ?_).isIso
      (isZero_positive (homotopyCofiber φ) i hi)
    intro j hij
    exact isZero_positive F j (by change i + 1 = j at hij; omega)
  · let n := (-i).toNat
    have hn : shape.f n = i := by
      change 0 - (((-i).toNat : ℕ) : ℤ) = i
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    rw [← hn]
    cases n with
    | zero => exact comparison_zero_isIso φ
    | succ n => rw [comparison_image]; infer_instance

theorem comparison_isIso : IsIso (comparison φ) := by
  let (i : ℤ) : IsIso ((comparison φ).f i) := comparison_component_isIso φ i
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : (homotopyCofiber φ).extend shape ≅ CochainComplex.mappingCone (extendedMap φ) := by
  letI := comparison_isIso φ
  exact (asIso (comparison φ)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NonpositiveConeExtension
