import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSheafificationCharts

/-! # Line Bundle Associator -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleAssociator.Construction

noncomputable section

/-! Associativity of tensor products of line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance lineBundleAssociatorMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

theorem isIso_presheafTensorMap_app {X : Scheme.{u}}
    {P P' Q Q' : X.PresheafOfModules} (a : P ⟶ P') (b : Q ⟶ Q') (U : X.Opens)
    [IsIso (a.app (.op U))] [IsIso (b.app (.op U))] : IsIso ((a ⊗ₘ b).app (.op U)) := by
  let ea : (P.obj (.op U) : ModuleCat Γ(X, U)) ≅ P'.obj (.op U) :=
    @asIso _ _ _ _ (a.app (.op U)) ‹IsIso (a.app (.op U))›
  let eb : (Q.obj (.op U) : ModuleCat Γ(X, U)) ≅ Q'.obj (.op U) :=
    @asIso _ _ _ _ (b.app (.op U)) ‹IsIso (b.app (.op U))›
  let e : (P.obj (.op U) ⊗ Q.obj (.op U) : ModuleCat Γ(X, U)) ≅
      (P'.obj (.op U) ⊗ Q'.obj (.op U) : ModuleCat Γ(X, U)) := ea ⊗ᵢ eb
  exact e.isIso_hom

def tripleTensorLeftMap {X : Scheme.{u}} (L M N : X.Modules) :
    (L.val ⊗ M.val) ⊗ N.val ⟶ (SheafTensor.Construction.sheafTensor (SheafTensor.Construction.sheafTensor L M) N).val :=
  (SheafRestriction.Construction.moduleSheafificationUnit (L.val ⊗ M.val) ⊗ₘ 𝟙 N.val) ≫
    SheafRestriction.Construction.moduleSheafificationUnit ((SheafTensor.Construction.sheafTensor L M).val ⊗ N.val)

def tripleTensorRightMap {X : Scheme.{u}} (L M N : X.Modules) :
    L.val ⊗ (M.val ⊗ N.val) ⟶ (SheafTensor.Construction.sheafTensor L (SheafTensor.Construction.sheafTensor M N)).val :=
  (𝟙 L.val ⊗ₘ SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val)) ≫
    SheafRestriction.Construction.moduleSheafificationUnit (L.val ⊗ (SheafTensor.Construction.sheafTensor M N).val)

theorem isIso_tripleTensorLeftLift {X : Scheme.{u}} {L M N : X.Modules}
    (hL : LineBundle.Construction.IsLineBundle L) (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    IsIso (SheafificationLocalIso.Construction.moduleSheafificationLift (tripleTensorLeftMap L M N)) := by
  apply SheafificationLocalIso.Construction.isIso_moduleSheafificationLift_of_local_app
  intro x
  obtain ⟨U, hxU, hU⟩ := TensorSheafificationCharts.Construction.tensorSheafificationUnit_locally_isIso_app hL hM x
  obtain ⟨V, hxV, hV⟩ := TensorSheafificationCharts.Construction.tensorSheafificationUnit_locally_isIso_app (TensorRestriction.Construction.isLineBundle_sheafTensor hL hM) hN x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun W hW ↦ ?_⟩
  have h₁ := hU W (hW.trans inf_le_left)
  have h₂ := hV W (hW.trans inf_le_right)
  have hid : IsIso ((𝟙 N.val : N.val ⟶ N.val).app (.op W)) := by
    change IsIso (𝟙 (N.val.obj (.op W)))
    infer_instance
  have ht := @isIso_presheafTensorMap_app X _ _ _ _
    (SheafRestriction.Construction.moduleSheafificationUnit (L.val ⊗ M.val)) (𝟙 N.val) W h₁ hid
  exact IsIso.comp_isIso' ht h₂

theorem isIso_tripleTensorRightLift {X : Scheme.{u}} {L M N : X.Modules}
    (hL : LineBundle.Construction.IsLineBundle L) (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    IsIso (SheafificationLocalIso.Construction.moduleSheafificationLift (tripleTensorRightMap L M N)) := by
  apply SheafificationLocalIso.Construction.isIso_moduleSheafificationLift_of_local_app
  intro x
  obtain ⟨U, hxU, hU⟩ := TensorSheafificationCharts.Construction.tensorSheafificationUnit_locally_isIso_app hM hN x
  obtain ⟨V, hxV, hV⟩ := TensorSheafificationCharts.Construction.tensorSheafificationUnit_locally_isIso_app hL (TensorRestriction.Construction.isLineBundle_sheafTensor hM hN) x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun W hW ↦ ?_⟩
  have h₁ := hU W (hW.trans inf_le_left)
  have h₂ := hV W (hW.trans inf_le_right)
  have hid : IsIso ((𝟙 L.val : L.val ⟶ L.val).app (.op W)) := by
    change IsIso (𝟙 (L.val.obj (.op W)))
    infer_instance
  have ht := @isIso_presheafTensorMap_app X _ _ _ _
    (𝟙 L.val) (SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val)) W hid h₁
  exact IsIso.comp_isIso' ht h₂

def lineBundleTensorAssociator {X : Scheme.{u}} {L M N : X.Modules}
    (hL : LineBundle.Construction.IsLineBundle L) (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    SheafTensor.Construction.sheafTensor (SheafTensor.Construction.sheafTensor L M) N ≅ SheafTensor.Construction.sheafTensor L (SheafTensor.Construction.sheafTensor M N) := by
  let eL := @asIso _ _ _ _ (SheafificationLocalIso.Construction.moduleSheafificationLift (tripleTensorLeftMap L M N))
    (isIso_tripleTensorLeftLift hL hM hN)
  let eR := @asIso _ _ _ _ (SheafificationLocalIso.Construction.moduleSheafificationLift (tripleTensorRightMap L M N))
    (isIso_tripleTensorRightLift hL hM hN)
  let F : X.PresheafOfModules ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  exact eL.symm ≪≫ F.mapIso (α_ L.val M.val N.val) ≪≫ eR

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleAssociator.Construction
