import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechD

/-! # Module Cech Pullback Short -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechPullbackShort

noncomputable section

/-! The geometric pullback of ordinary module Cech cochains as a map of
short complexes, including the degree-one differential. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ModuleCechPullback

variable {X Y S : Scheme.{u}}
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S) (h : f ≫ π = ρ) (M : X.Modules)
    {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)
    (r : κ → ι) (hr : ∀ j, V j ≤ f ⁻¹ᵁ U (r j))

include hr in
theorem triple_preimage (i j k : κ) :
    (V i ⊓ V j) ⊓ V k ≤ f ⁻¹ᵁ ((U (r i) ⊓ U (r j)) ⊓ U (r k)) := by
  intro y hy
  exact ⟨⟨hr i hy.1.1, hr j hy.1.2⟩, hr k hy.2⟩

def eval2 (i j k : ι) : OpenCechShortComplex.Construction.CubeCech.openModuleCechC2 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U →ₗ[Γ(S, ⊤)]
    (BaseModule.Construction.BaseModuleSheaf.sheaf π M).obj.obj (op ((U i ⊓ U j) ⊓ U k)) where
  toFun z := z i j k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def map2 : OpenCechShortComplex.Construction.CubeCech.openModuleCechC2 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U →ₗ[Γ(S, ⊤)]
    OpenCechShortComplex.Construction.CubeCech.openModuleCechC2 (BaseModule.Construction.BaseModuleSheaf.sheaf ρ ((Scheme.Modules.pullback f).obj M)) V :=
  LinearMap.pi fun i => LinearMap.pi fun j => LinearMap.pi fun k =>
    (ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M ((U (r i) ⊓ U (r j)) ⊓ U (r k))
      ((V i ⊓ V j) ⊓ V k) (triple_preimage f U V r hr i j k)).hom.comp
        (eval2 π M U (r i) (r j) (r k))

theorem differential_one (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U) :
    map2 f π ρ h M U V r hr (OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U z) =
      OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (BaseModule.Construction.BaseModuleSheaf.sheaf ρ ((Scheme.Modules.pullback f).obj M)) V
        (ModuleCechD.Construction.ModuleCechPullback.schemeCechPullback1 f π ρ h M U V r hr z) := by
  funext i j k
  let W := (U (r i) ⊓ U (r j)) ⊓ U (r k)
  let W' := (V i ⊓ V j) ⊓ V k
  have hW := triple_preimage f U V r hr i j k
  have hij := ModuleCechD.Construction.ModuleCechPullback.schemeCechPullback1_restrict f π ρ h M U V r hr z i j W W'
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) hW
  have hjk := ModuleCechD.Construction.ModuleCechPullback.schemeCechPullback1_restrict f π ρ h M U V r hr z j k W W'
    (inf_le_left.trans inf_le_right) inf_le_right
    (inf_le_left.trans inf_le_right) inf_le_right hW
  have hik := ModuleCechD.Construction.ModuleCechPullback.schemeCechPullback1_restrict f π ρ h M U V r hr z i k W W'
    (inf_le_left.trans inf_le_left) inf_le_right
    (inf_le_left.trans inf_le_left) inf_le_right hW
  change ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M W W' hW
    (CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U z (r i) (r j) W
        (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
      CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U z (r j) (r k) W
        (inf_le_left.trans inf_le_right) inf_le_right -
      CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U z (r i) (r k) W
        (inf_le_left.trans inf_le_left) inf_le_right) = _
  rw [map_sub, map_add]
  exact congrArg₂ (fun a b => a - b) (congrArg₂ (fun a b => a + b) hij.symm hjk.symm) hik.symm

def shortMap :
    OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U ⟶
      OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex (BaseModule.Construction.BaseModuleSheaf.sheaf ρ ((Scheme.Modules.pullback f).obj M)) V where
  τ₁ := ModuleCat.ofHom (ModuleCechD.Construction.ModuleCechPullback.schemeCechPullback0 f π ρ h M U V r hr)
  τ₂ := ModuleCat.ofHom (ModuleCechD.Construction.ModuleCechPullback.schemeCechPullback1 f π ρ h M U V r hr)
  τ₃ := ModuleCat.ofHom (map2 f π ρ h M U V r hr)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (ModuleCechD.Construction.ModuleCechPullback.schemeCechPullback_d0 f π ρ h M U V r hr z).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (differential_one f π ρ h M U V r hr z).symm

end Construction.ModuleCechPullback

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechPullbackShort
