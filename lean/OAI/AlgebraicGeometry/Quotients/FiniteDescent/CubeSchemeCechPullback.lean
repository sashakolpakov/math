import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeSectionsNaturality
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeOpenCechCocycles

/-! # Cube Scheme Cech Pullback -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeSchemeCechPullback.Construction.CubeCech

noncomputable section

/-! Pullback of low-degree Cech cochains along a morphism of schemes over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Y ⟶ X) (hh : h ≫ f = g)
    {ι : Type v} {κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (r : κ → ι) (hr : ∀ j, V j ≤ h ⁻¹ᵁ U (r j))

include hr in
theorem cechPullback_overlap_preimage (i j : κ) :
    V i ⊓ V j ≤ h ⁻¹ᵁ (U (r i) ⊓ U (r j)) := by
  intro y hy
  exact ⟨hr i hy.1, hr j hy.2⟩

def schemeCechPullback0 :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U →ₗ[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V :=
  LinearMap.pi fun j ↦ (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap f g h hh (U (r j)) (V j) (hr j)).comp
    (LinearMap.proj (r j))

def schemeCech1Eval (i j : ι) :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U →ₗ[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op (U i ⊓ U j)) where
  toFun z := z i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def schemeCechPullback1 :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U →ₗ[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap f g h hh (U (r i) ⊓ U (r j)) (V i ⊓ V j)
      (cechPullback_overlap_preimage h U V r hr i j)).comp
        (schemeCech1Eval f U (r i) (r j))

theorem schemeCechPullback_d0 (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) :
    schemeCechPullback1 f g h hh U V r hr
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U x) =
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V
        (schemeCechPullback0 f g h hh U V r hr x) := by
  funext i j
  change CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap f g h hh (U (r i) ⊓ U (r j)) (V i ⊓ V j) _
    ((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.map (homOfLE inf_le_right).op (x (r j)) -
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.map (homOfLE inf_le_left).op (x (r i))) = _
  rw [map_sub]
  exact congrArg₂ (fun a b ↦ a - b)
    (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap_restrict f g h hh (homOfLE inf_le_right) (homOfLE inf_le_right)
      (hr j) (cechPullback_overlap_preimage h U V r hr i j) (x (r j)))
    (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap_restrict f g h hh (homOfLE inf_le_left) (homOfLE inf_le_left)
      (hr i) (cechPullback_overlap_preimage h U V r hr i j) (x (r i)))

theorem schemeCechPullback1_restrict
    (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) (i j : κ)
    (W : X.Opens) (W' : Y.Opens) (hi : W ≤ U (r i)) (hj : W ≤ U (r j))
    (hi' : W' ≤ V i) (hj' : W' ≤ V j) (hW : W' ≤ h ⁻¹ᵁ W) :
    CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V
      (schemeCechPullback1 f g h hh U V r hr z) i j W' hi' hj' =
      CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap f g h hh W W' hW
        (CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U z (r i) (r j) W hi hj) :=
  (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap_restrict f g h hh (homOfLE (le_inf hi hj)) (homOfLE (le_inf hi' hj'))
    (cechPullback_overlap_preimage h U V r hr i j) hW (z (r i) (r j))).symm

theorem schemeCechPullback_isCocycle
    (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (hz : CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U z) :
    CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V
      (schemeCechPullback1 f g h hh U V r hr z) := by
  intro i j l W' hi' hj' hl'
  let W := (U (r i) ⊓ U (r j)) ⊓ U (r l)
  have hi : W ≤ U (r i) := inf_le_left.trans inf_le_left
  have hj : W ≤ U (r j) := inf_le_left.trans inf_le_right
  have hl : W ≤ U (r l) := inf_le_right
  have hW : W' ≤ h ⁻¹ᵁ W := by
    intro y hy
    exact ⟨⟨hr i (hi' hy), hr j (hj' hy)⟩, hr l (hl' hy)⟩
  have hij := schemeCechPullback1_restrict f g h hh U V r hr z i j W W' hi hj hi' hj' hW
  have hjl := schemeCechPullback1_restrict f g h hh U V r hr z j l W W' hj hl hj' hl' hW
  have hil := schemeCechPullback1_restrict f g h hh U V r hr z i l W W' hi hl hi' hl' hW
  exact (congrArg₂ (fun a b ↦ a + b) hij hjl).trans
    ((map_add (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap f g h hh W W' hW) _ _).symm.trans
      ((congrArg (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap f g h hh W W' hW)
        (hz (r i) (r j) (r l) W hi hj hl)).trans hil.symm))

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeSchemeCechPullback.Construction.CubeCech
