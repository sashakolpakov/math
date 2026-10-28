import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleLocalIso

/-! # Line Bundle Tensor Pullback -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleTensorPullback.Construction

noncomputable section

/-! Tensor products of line bundles commute with arbitrary pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIso_pullbackSheafTensorMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules)
    [IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap g M N)]
    [IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullback g).obj N))] :
    IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap (f ≫ g) M N) := by
  have := TensorUnit.Construction.sheafTensorMap_isIso ((Scheme.Modules.pullbackComp f g).inv.app M)
    ((Scheme.Modules.pullbackComp f g).inv.app N)
  have : IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap (f ≫ g) M N ≫
      TensorFunctoriality.Construction.sheafTensorMap ((Scheme.Modules.pullbackComp f g).inv.app M)
        ((Scheme.Modules.pullbackComp f g).inv.app N)) := by
    rw [← TensorComposition.Construction.pullbackSheafTensorMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (TensorFunctoriality.Construction.sheafTensorMap ((Scheme.Modules.pullbackComp f g).inv.app M)
      ((Scheme.Modules.pullbackComp f g).inv.app N))

theorem isIso_map_pullbackSheafTensorMap {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules)
    [IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap (f ≫ g) M N)]
    [IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullback g).obj N))] :
    IsIso ((Scheme.Modules.pullback f).map (TensorFunctoriality.Construction.pullbackSheafTensorMap g M N)) := by
  have := TensorUnit.Construction.sheafTensorMap_isIso ((Scheme.Modules.pullbackComp f g).inv.app M)
    ((Scheme.Modules.pullbackComp f g).inv.app N)
  have : IsIso ((Scheme.Modules.pullbackComp f g).inv.app (SheafTensor.Construction.sheafTensor M N) ≫
      (Scheme.Modules.pullback f).map (TensorFunctoriality.Construction.pullbackSheafTensorMap g M N) ≫
        TensorFunctoriality.Construction.pullbackSheafTensorMap f ((Scheme.Modules.pullback g).obj M)
          ((Scheme.Modules.pullback g).obj N)) := by
    rw [TensorComposition.Construction.pullbackSheafTensorMap_comp]
    infer_instance
  have : IsIso ((Scheme.Modules.pullback f).map (TensorFunctoriality.Construction.pullbackSheafTensorMap g M N) ≫
      TensorFunctoriality.Construction.pullbackSheafTensorMap f ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N)) :=
    IsIso.of_isIso_comp_left ((Scheme.Modules.pullbackComp f g).inv.app (SheafTensor.Construction.sheafTensor M N)) _
  exact IsIso.of_isIso_comp_right _
    (TensorFunctoriality.Construction.pullbackSheafTensorMap f ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullback g).obj N))

theorem isIso_pullbackSheafTensorMap_of_isLineBundle {X Y : Scheme.{u}}
    (f : X ⟶ Y) {M N : Y.Modules} (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f M N) := by
  apply ModuleLocalIso.Construction.isIso_of_locally_isIso_pullback
  intro x
  obtain ⟨V₁, hx₁, ⟨e₁⟩⟩ := hM (f x)
  obtain ⟨V₂, hx₂, ⟨e₂⟩⟩ := hN (f x)
  let V := V₁ ⊓ V₂
  let U := f ⁻¹ᵁ V
  let r := f ∣_ V
  let eM := TensorRestriction.Construction.restrictLineBundleTrivialization (show V ≤ V₁ from inf_le_left) e₁
  let eN := TensorRestriction.Construction.restrictLineBundleTrivialization (show V ≤ V₂ from inf_le_right) e₂
  have := TensorOpenComparison.Construction.isIso_pullbackSheafTensorMap_of_openImmersion V.ι M N
  have := TensorUnit.Construction.isIso_pullbackSheafTensorMap_of_trivial r eM eN
  have hr := isIso_pullbackSheafTensorMap_comp r V.ι M N
  have hcomp : IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap (U.ι ≫ f) M N) := by
    exact morphismRestrict_ι f V ▸ hr
  have := TensorOpenComparison.Construction.isIso_pullbackSheafTensorMap_of_openImmersion U.ι
    ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
  exact ⟨U, ⟨hx₁, hx₂⟩, isIso_map_pullbackSheafTensorMap U.ι f M N⟩

def pullbackLineBundleTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    (Scheme.Modules.pullback f).obj (SheafTensor.Construction.sheafTensor M N) ≅
      SheafTensor.Construction.sheafTensor ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  have := isIso_pullbackSheafTensorMap_of_isLineBundle f hM hN
  exact asIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f M N)

def pullbackLineBundleTensorPowerIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (hM : LineBundle.Construction.IsLineBundle M) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (TensorRestriction.Construction.sheafTensorPower M n) ≅
      TensorRestriction.Construction.sheafTensorPower ((Scheme.Modules.pullback f).obj M) n := by
  induction n with
  | zero => exact LineBundle.Construction.pullbackStructureSheafIso f
  | succ n ih =>
    exact pullbackLineBundleTensorIso f (TensorRestriction.Construction.isLineBundle_sheafTensorPower hM n) hM ≪≫
      SheafTensor.Construction.sheafTensorCongr ih (Iso.refl _)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleTensorPullback.Construction
