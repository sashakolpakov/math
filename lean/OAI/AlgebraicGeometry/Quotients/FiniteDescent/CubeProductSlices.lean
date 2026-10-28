import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePointEvaluation
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSections

/-! # Cube Product Slices -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSlices.Construction.CubeCech

noncomputable section

/-! Restricting product functions along a rational-point slice. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

theorem scheme_appLE_congr_morphism {A B : Scheme.{u}} {a b : A ⟶ B} (hab : a = b)
    (U : B.Opens) (V : A.Opens) (ha : V ≤ a ⁻¹ᵁ U) (hb : V ≤ b ⁻¹ᵁ U) :
    a.appLE U V ha = b.appLE U V hb := by
  subst b
  rfl

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ Y) (hs : s ≫ g = 𝟙 _)

def productSliceLeft : X ⟶ pullback f g :=
  pullback.lift (𝟙 X) (f ≫ s) (by rw [Category.id_comp, Category.assoc, hs, Category.comp_id])

theorem productSliceLeft_fst : productSliceLeft f g s hs ≫ pullback.fst f g = 𝟙 X :=
  pullback.lift_fst _ _ _

theorem productSliceLeft_snd : productSliceLeft f g s hs ≫ pullback.snd f g = f ≫ s :=
  pullback.lift_snd _ _ _

theorem productSliceLeft_rectangle_preimage (U : X.Opens) (V : Y.Opens)
    (hV : ⊤ ≤ s ⁻¹ᵁ V) :
    U ≤ productSliceLeft f g s hs ⁻¹ᵁ CubeProductSections.Construction.CubeCech.productRectangle f g U V := by
  intro x hx
  have hfst := congrArg (fun h : X ⟶ X ↦ h x) (productSliceLeft_fst f g s hs)
  have hsnd := congrArg (fun h : X ⟶ Y ↦ h x) (productSliceLeft_snd f g s hs)
  change (pullback.fst f g) (productSliceLeft f g s hs x) = x at hfst
  change (pullback.snd f g) (productSliceLeft f g s hs x) = s (f x) at hsnd
  change (pullback.fst f g) (productSliceLeft f g s hs x) ∈ U ∧
    (pullback.snd f g) (productSliceLeft f g s hs x) ∈ V
  rw [hfst, hsnd]
  exact ⟨hx, hV (by trivial)⟩

abbrev productSliceLeftSectionMap (U : X.Opens) (V : Y.Opens) (hV : ⊤ ≤ s ⁻¹ᵁ V) :
    Γ(pullback f g, CubeProductSections.Construction.CubeCech.productRectangle f g U V) ⟶ Γ(X, U) :=
  (productSliceLeft f g s hs).appLE _ U (productSliceLeft_rectangle_preimage f g s hs U V hV)

theorem productSliceLeftSectionMap_left (U : X.Opens) (V : Y.Opens) (hV : ⊤ ≤ s ⁻¹ᵁ V) :
    CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g U V ≫ productSliceLeftSectionMap f g s hs U V hV = 𝟙 _ := by
  change (pullback.fst f g).appLE U _ inf_le_left ≫
    (productSliceLeft f g s hs).appLE _ U _ = _
  rw [Scheme.Hom.appLE_comp_appLE]
  refine (scheme_appLE_congr_morphism (productSliceLeft_fst f g s hs) U U _ le_rfl).trans ?_
  change (𝟙 Γ(X, U)) ≫ X.presheaf.map (𝟙 (op U)) = 𝟙 _
  rw [X.presheaf.map_id, Category.id_comp]

theorem productSliceLeftSectionMap_right (U : X.Opens) (V : Y.Opens) (hV : ⊤ ≤ s ⁻¹ᵁ V) :
    CubeProductSections.Construction.CubeCech.productRectangleRightMap f g U V ≫ productSliceLeftSectionMap f g s hs U V hV =
      CommRingCat.ofHom (CubePointEvaluation.Construction.CubeCech.pointEvaluationRingHom s V hV) ≫ CommRingCat.ofHom (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants f U) := by
  change (pullback.snd f g).appLE V _ inf_le_right ≫
    (productSliceLeft f g s hs).appLE _ U _ = _
  rw [Scheme.Hom.appLE_comp_appLE]
  have hUV : U ≤ (f ≫ s) ⁻¹ᵁ V := by
    intro x _
    exact hV (by trivial)
  refine (scheme_appLE_congr_morphism (productSliceLeft_snd f g s hs) V U _ hUV).trans ?_
  rw [CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants_eq_appLE]
  change (f ≫ s).appLE V U _ =
    (s.appLE V ⊤ hV ≫ (Scheme.ΓSpecIso (.of k)).hom) ≫
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Scheme.Hom.appLE_comp_appLE f s V ⊤ U hV (by simp)).symm

open scoped TensorProduct in
theorem productSliceLeftSectionMap_tmul (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hsV : ⊤ ≤ s ⁻¹ᵁ V)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U))
    (y : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V)) :
    productSliceLeftSectionMap f g s hs U V hsV
      (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U V hU hV (x ⊗ₜ[k] y)) =
      CubePointEvaluation.Construction.CubeCech.pointEvaluationLinearMap g s hs V hsV y • x := by
  let x' : Γ(X, U) := x
  let y' : Γ(Y, V) := y
  change productSliceLeftSectionMap f g s hs U V hsV
    (CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv f g U V hU hV (x' ⊗ₜ[k] y')) =
      CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants f U (CubePointEvaluation.Construction.CubeCech.pointEvaluationRingHom s V hsV y') * x'
  refine (congrArg (productSliceLeftSectionMap f g s hs U V hsV)
    (CubeProductSections.Construction.CubeCech.productRectangleSectionsEquiv_tmul f g U V hU hV x' y')).trans ?_
  rw [map_mul]
  have hleft := congrArg (fun q : Γ(X, U) ⟶ Γ(X, U) ↦ q x')
    (productSliceLeftSectionMap_left f g s hs U V hsV)
  have hright := congrArg (fun q : Γ(Y, V) ⟶ Γ(X, U) ↦ q y')
    (productSliceLeftSectionMap_right f g s hs U V hsV)
  change productSliceLeftSectionMap f g s hs U V hsV (CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g U V x') = x' at hleft
  change productSliceLeftSectionMap f g s hs U V hsV (CubeProductSections.Construction.CubeCech.productRectangleRightMap f g U V y') =
    CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants f U (CubePointEvaluation.Construction.CubeCech.pointEvaluationRingHom s V hsV y') at hright
  rw [hleft, hright, mul_comm]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSlices.Construction.CubeCech
