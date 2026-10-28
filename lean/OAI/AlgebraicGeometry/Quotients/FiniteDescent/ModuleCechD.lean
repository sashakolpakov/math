import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechShortComplex

/-! # Module Cech D -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechD

noncomputable section

/-! Pullback of low-degree Cech cochains of a scheme module over a fixed base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

namespace Construction.ModuleCechPullback

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y S : Scheme.{u}}
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S) (h : f ≫ π = ρ) (M : X.Modules)
    {ι : Type u} {κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)
    (r : κ → ι) (hr : ∀ j, V j ≤ f ⁻¹ᵁ U (r j))

include hr in
theorem cechPullback_overlap_preimage (i j : κ) :
    V i ⊓ V j ≤ f ⁻¹ᵁ (U (r i) ⊓ U (r j)) := by
  intro y hy
  exact ⟨hr i hy.1, hr j hy.2⟩

def schemeCechPullback0 :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U →ₗ[Γ(S, ⊤)]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (BaseModule.Construction.BaseModuleSheaf.sheaf ρ ((Scheme.Modules.pullback f).obj M)) V :=
  LinearMap.pi fun j ↦ (ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (U (r j)) (V j) (hr j)).hom.comp
    (LinearMap.proj (r j))

def schemeCech1Eval (i j : ι) :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U →ₗ[Γ(S, ⊤)]
      (BaseModule.Construction.BaseModuleSheaf.sheaf π M).obj.obj (op (U i ⊓ U j)) where
  toFun z := z i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def schemeCechPullback1 :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U →ₗ[Γ(S, ⊤)]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (BaseModule.Construction.BaseModuleSheaf.sheaf ρ ((Scheme.Modules.pullback f).obj M)) V :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (U (r i) ⊓ U (r j)) (V i ⊓ V j)
      (cechPullback_overlap_preimage f U V r hr i j)).hom.comp
        (schemeCech1Eval π M U (r i) (r j))

theorem schemeCechPullback_d0 (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U) :
    schemeCechPullback1 f π ρ h M U V r hr
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U x) =
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (BaseModule.Construction.BaseModuleSheaf.sheaf ρ ((Scheme.Modules.pullback f).obj M)) V
        (schemeCechPullback0 f π ρ h M U V r hr x) := by
  funext i j
  change ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M (U (r i) ⊓ U (r j)) (V i ⊓ V j) _
    ((BaseModule.Construction.BaseModuleSheaf.sheaf π M).obj.map (homOfLE inf_le_right).op (x (r j)) -
      (BaseModule.Construction.BaseModuleSheaf.sheaf π M).obj.map (homOfLE inf_le_left).op (x (r i))) = _
  rw [map_sub]
  exact congrArg₂ (fun a b ↦ a - b)
    (ModuleSections.Construction.ModuleSectionsOver.restrict f π ρ h M (homOfLE inf_le_right) (homOfLE inf_le_right)
      (hr j) (cechPullback_overlap_preimage f U V r hr i j) (x (r j)))
    (ModuleSections.Construction.ModuleSectionsOver.restrict f π ρ h M (homOfLE inf_le_left) (homOfLE inf_le_left)
      (hr i) (cechPullback_overlap_preimage f U V r hr i j) (x (r i)))

theorem schemeCechPullback1_restrict
    (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U) (i j : κ)
    (W : X.Opens) (W' : Y.Opens) (hi : W ≤ U (r i)) (hj : W ≤ U (r j))
    (hi' : W' ≤ V i) (hj' : W' ≤ V j) (hW : W' ≤ f ⁻¹ᵁ W) :
    CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 (BaseModule.Construction.BaseModuleSheaf.sheaf ρ ((Scheme.Modules.pullback f).obj M)) V
      (schemeCechPullback1 f π ρ h M U V r hr z) i j W' hi' hj' =
      ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M W W' hW
        (CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U z (r i) (r j) W hi hj) :=
  (ModuleSections.Construction.ModuleSectionsOver.restrict f π ρ h M (homOfLE (le_inf hi hj)) (homOfLE (le_inf hi' hj'))
    (cechPullback_overlap_preimage f U V r hr i j) hW (z (r i) (r j))).symm

theorem schemeCechPullback_isCocycle
    (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U)
    (hz : CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U z) :
    CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (BaseModule.Construction.BaseModuleSheaf.sheaf ρ ((Scheme.Modules.pullback f).obj M)) V
      (schemeCechPullback1 f π ρ h M U V r hr z) := by
  intro i j l W' hi' hj' hl'
  let W := (U (r i) ⊓ U (r j)) ⊓ U (r l)
  have hi : W ≤ U (r i) := inf_le_left.trans inf_le_left
  have hj : W ≤ U (r j) := inf_le_left.trans inf_le_right
  have hl : W ≤ U (r l) := inf_le_right
  have hW : W' ≤ f ⁻¹ᵁ W := by
    intro y hy
    exact ⟨⟨hr i (hi' hy), hr j (hj' hy)⟩, hr l (hl' hy)⟩
  have hij := schemeCechPullback1_restrict f π ρ h M U V r hr z i j W W' hi hj hi' hj' hW
  have hjl := schemeCechPullback1_restrict f π ρ h M U V r hr z j l W W' hj hl hj' hl' hW
  have hil := schemeCechPullback1_restrict f π ρ h M U V r hr z i l W W' hi hl hi' hl' hW
  exact (congrArg₂ (fun a b ↦ a + b) hij hjl).trans
    ((map_add (ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M W W' hW).hom _ _).symm.trans
      ((congrArg (ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M W W' hW)
        (hz (r i) (r j) (r l) W hi hj hl)).trans hil.symm))

end Construction.ModuleCechPullback

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechD
