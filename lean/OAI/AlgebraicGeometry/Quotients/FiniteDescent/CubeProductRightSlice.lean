import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSliceLinear

/-! # Cube Product Right Slice -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductRightSlice.Construction.CubeCech

noncomputable section

/-! Evaluation on a rational-point slice in the first factor of a product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)

def productSliceRight : Y ⟶ pullback f g :=
  pullback.lift (g ≫ s) (𝟙 Y) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

theorem productSliceRight_fst : productSliceRight f g s hs ≫ pullback.fst f g = g ≫ s :=
  pullback.lift_fst _ _ _

theorem productSliceRight_snd : productSliceRight f g s hs ≫ pullback.snd f g = 𝟙 Y :=
  pullback.lift_snd _ _ _

theorem productSliceRight_rectangle_preimage (U : X.Opens) (V : Y.Opens)
    (hU : ⊤ ≤ s ⁻¹ᵁ U) :
    V ≤ productSliceRight f g s hs ⁻¹ᵁ CubeProductSections.Construction.CubeCech.productRectangle f g U V := by
  intro y hy
  have hfst := congrArg (fun h : Y ⟶ X ↦ h y) (productSliceRight_fst f g s hs)
  have hsnd := congrArg (fun h : Y ⟶ Y ↦ h y) (productSliceRight_snd f g s hs)
  change (pullback.fst f g) (productSliceRight f g s hs y) = s (g y) at hfst
  change (pullback.snd f g) (productSliceRight f g s hs y) = y at hsnd
  change (pullback.fst f g) (productSliceRight f g s hs y) ∈ U ∧
    (pullback.snd f g) (productSliceRight f g s hs y) ∈ V
  rw [hfst, hsnd]
  exact ⟨hU (by trivial), hy⟩

abbrev productSliceRightSectionMap (U : X.Opens) (V : Y.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U) :
    Γ(pullback f g, CubeProductSections.Construction.CubeCech.productRectangle f g U V) ⟶ Γ(Y, V) :=
  (productSliceRight f g s hs).appLE _ V (productSliceRight_rectangle_preimage f g s hs U V hU)

theorem productSliceRightSectionMap_right (U : X.Opens) (V : Y.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U) :
    CubeProductSections.Construction.CubeCech.productRectangleRightMap f g U V ≫ productSliceRightSectionMap f g s hs U V hU = 𝟙 _ := by
  change (pullback.snd f g).appLE V _ inf_le_right ≫
    (productSliceRight f g s hs).appLE _ V _ = _
  rw [Scheme.Hom.appLE_comp_appLE]
  refine (CubeProductSlices.Construction.CubeCech.scheme_appLE_congr_morphism (productSliceRight_snd f g s hs) V V _ le_rfl).trans ?_
  change (𝟙 Γ(Y, V)) ≫ Y.presheaf.map (𝟙 (op V)) = 𝟙 _
  rw [Y.presheaf.map_id, Category.id_comp]

theorem productSliceRightSectionMap_left (U : X.Opens) (V : Y.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U) :
    CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g U V ≫ productSliceRightSectionMap f g s hs U V hU =
      CommRingCat.ofHom (CubePointEvaluation.Construction.CubeCech.pointEvaluationRingHom s U hU) ≫ CommRingCat.ofHom (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants g V) := by
  change (pullback.fst f g).appLE U _ inf_le_left ≫
    (productSliceRight f g s hs).appLE _ V _ = _
  rw [Scheme.Hom.appLE_comp_appLE]
  have hVU : V ≤ (g ≫ s) ⁻¹ᵁ U := by intro y _; exact hU (by trivial)
  refine (CubeProductSlices.Construction.CubeCech.scheme_appLE_congr_morphism (productSliceRight_fst f g s hs) U V _ hVU).trans ?_
  rw [CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants_eq_appLE]
  change (g ≫ s).appLE U V _ =
    (s.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of k)).hom) ≫
      (Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ V _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Scheme.Hom.appLE_comp_appLE g s U ⊤ V hU (by simp)).symm

theorem productSliceRightSectionMap_tmul (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hsU : ⊤ ≤ s ⁻¹ᵁ U)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U))
    (y : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V)) :
    productSliceRightSectionMap f g s hs U V hsU
      (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U V hU hV (x ⊗ₜ[k] y)) =
      CubePointEvaluation.Construction.CubeCech.pointEvaluationLinearMap f s hs U hsU x • y := by
  let x' : Γ(X, U) := x
  let y' : Γ(Y, V) := y
  change productSliceRightSectionMap f g s hs U V hsU
    (CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv f g U V hU hV (x' ⊗ₜ[k] y')) =
      CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants g V (CubePointEvaluation.Construction.CubeCech.pointEvaluationRingHom s U hsU x') * y'
  refine (congrArg (productSliceRightSectionMap f g s hs U V hsU)
    (CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv_tmul f g U V hU hV x' y')).trans ?_
  rw [map_mul]
  have hleft := congrArg (fun q : Γ(X, U) ⟶ Γ(Y, V) ↦ q x')
    (productSliceRightSectionMap_left f g s hs U V hsU)
  have hright := congrArg (fun q : Γ(Y, V) ⟶ Γ(Y, V) ↦ q y')
    (productSliceRightSectionMap_right f g s hs U V hsU)
  exact congrArg₂ (fun a b ↦ a * b) hleft hright

theorem productSliceRight_over : productSliceRight f g s hs ≫ (pullback.fst f g ≫ f) = g := by
  rw [← Category.assoc, productSliceRight_fst, Category.assoc, hs, Category.comp_id]

def productSliceRightLinearMap (U : X.Opens) (V : Y.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g U V)) →ₗ[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V) :=
  (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsCongr (productSliceRight_over f g s hs) V).toLinearMap.comp
    (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsPullback (pullback.fst f g ≫ f) (productSliceRight f g s hs)
      (CubeProductSections.Construction.CubeCech.productRectangle f g U V) V (productSliceRight_rectangle_preimage f g s hs U V hU))

theorem productSliceRightLinearMap_apply (U : X.Opens) (V : Y.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g U V))) :
    (productSliceRightLinearMap f g s hs U V hU x : Γ(Y, V)) =
      productSliceRightSectionMap f g s hs U V hU x := by
  exact (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsCongr_apply (productSliceRight_over f g s hs) V _).trans
    (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsPullback_apply _ _ _ _ _ x)

theorem productSliceRightLinearMap_tensor (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hsU : ⊤ ≤ s ⁻¹ᵁ U)
    (z : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) ⊗[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V)) :
    productSliceRightLinearMap f g s hs U V hsU
      (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U V hU hV z) =
      TensorProduct.lid k _ (TensorProduct.map (CubePointEvaluation.Construction.CubeCech.pointEvaluationLinearMap f s hs U hsU) LinearMap.id z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x y =>
    exact (productSliceRightLinearMap_apply f g s hs U V hsU _).trans
      (productSliceRightSectionMap_tmul f g s hs U V hU hV hsU x y)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductRightSlice.Construction.CubeCech
