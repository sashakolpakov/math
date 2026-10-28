import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.KernelSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.UnitAdjunction

/-! # Ideal Pullback Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealPullbackMap.BundleCycles

noncomputable section

/-! The canonical map from the pullback of an actual scheme ideal
to the ideal in a commuting square, constructed by kernels and the genuine
module pullback adjunction. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Z X' Z' : Scheme.{0}} (i : Z ⟶ X) (j : Z' ⟶ X')
    (f : X' ⟶ X) (g : Z' ⟶ Z) (h : g ≫ i = j ≫ f)

include g h in
theorem schemeIdealSquare_composite_zero :
    (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i ≫ SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f) ≫
      (Scheme.Modules.pushforward f).map (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap j) = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap j).app (f ⁻¹ᵁ U)
    ((SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f).app U ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i).app U s)) = 0
  let a : Γ(X, U) := (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i).app U s
  have ha : a ∈ RingHom.ker (i.app U).hom := by
    change (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i).app U s ∈ RingHom.ker (i.app U).hom
    rw [← IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply i U s]
    exact IdealModule.BundleCycles.schemeIdealModuleSectionLinear_mem i U s
  have h₁ := congrArg ((SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap j).app (f ⁻¹ᵁ U))
    (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap_apply f U a)
  have h₂ := SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap_apply j (f ⁻¹ᵁ U) (f.app U a)
  exact (h₁.trans h₂).trans (KernelSquare.BundleCycles.schemeKernelSquare_mem i j f g h U a ha)

def schemeIdealSquareAdjoint : SchemeIdealModule.BundleCycles.schemeIdealModule i ⟶
    (Scheme.Modules.pushforward f).obj (SchemeIdealModule.BundleCycles.schemeIdealModule j) :=
  kernel.lift ((Scheme.Modules.pushforward f).map (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap j))
    (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i ≫ SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f) (schemeIdealSquare_composite_zero i j f g h) ≫
      (PreservesKernel.iso (Scheme.Modules.pushforward f) (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap j)).inv

theorem schemeIdealSquareAdjoint_inclusion :
    schemeIdealSquareAdjoint i j f g h ≫ (Scheme.Modules.pushforward f).map (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion j) =
      SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i ≫ SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f := by
  let F := Scheme.Modules.pushforward f
  let δ := SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap j
  let ψ := SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i ≫ SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f
  let ℓ := kernel.lift (F.map δ) ψ (schemeIdealSquare_composite_zero i j f g h)
  let e := PreservesKernel.iso F δ
  change (ℓ ≫ e.inv) ≫ F.map (kernel.ι δ) = ψ
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => ℓ ≫ k) (PreservesKernel.iso_inv_ι F δ)).trans (kernel.lift_ι _ _ _))

def schemeIdealPullbackMap : (Scheme.Modules.pullback f).obj (SchemeIdealModule.BundleCycles.schemeIdealModule i) ⟶ SchemeIdealModule.BundleCycles.schemeIdealModule j :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (schemeIdealSquareAdjoint i j f g h)

theorem schemeIdealPullbackMap_adjunction :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (schemeIdealPullbackMap i j f g h) =
      schemeIdealSquareAdjoint i j f g h :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

theorem schemeIdealPullbackMap_inclusion :
    schemeIdealPullbackMap i j f g h ≫ SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion j =
      (Scheme.Modules.pullback f).map (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) ≫ (LineBundle.OpenRestriction.Cycles.modulePullbackUnitIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, schemeIdealPullbackMap_adjunction,
    Adjunction.homEquiv_naturality_left, Module.UnitAdjunction.BundleCycles.modulePullbackUnitIso_adjunction,
    schemeIdealSquareAdjoint_inclusion]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealPullbackMap.BundleCycles
