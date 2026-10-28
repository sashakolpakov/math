import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechPullbackShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoefficient

/-! # Module Cech Sections -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechSections

noncomputable section

/-! Geometric Cech pullback commutes with maps of module coefficients. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ModuleCechNaturality

variable {X Y S : Scheme.{u}}
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S) (h : f ≫ π = ρ)
    {M N : X.Modules} (a : M ⟶ N)

theorem sections (U : X.Opens) (V : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    ModuleSections.Construction.ModuleSectionsOver.map f π ρ h N U V hVU (a.app U s) =
      ((Scheme.Modules.pullback f).map a).app V
        (ModuleSections.Construction.ModuleSectionsOver.map f π ρ h M U V hVU s) := by
  rw [ModuleSections.Construction.ModuleSectionsOver.map_apply, ModuleSections.Construction.ModuleSectionsOver.map_apply]
  change ((Scheme.Modules.pullback f).obj N).presheaf.map (homOfLE hVU).op
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f N U (a.val.app (op U) s)) = _
  rw [PullbackSectionRestrict.Construction.PullbackSectionCoefficients.naturality]
  exact (PresheafOfModules.naturality_apply ((Scheme.Modules.pullback f).map a).val
    (homOfLE hVU).op (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s)).symm

theorem shortMap {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)
    (r : κ → ι) (hr : ∀ j, V j ≤ f ⁻¹ᵁ U (r j)) :
    ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ h M U V r hr ≫
        (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor ρ V).map ((Scheme.Modules.pullback f).map a) =
      (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor π U).map a ≫
        ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ h N U V r hr := by
  apply ShortComplex.hom_ext
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    exact (sections f π ρ h a (U (r i)) (V i) (hr i) (z (r i))).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i j
    exact (sections f π ρ h a _ _
      (ModuleCechD.Construction.ModuleCechPullback.cechPullback_overlap_preimage f U V r hr i j) (z (r i) (r j))).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i j k
    exact (sections f π ρ h a _ _
      (ModuleCechPullbackShort.Construction.ModuleCechPullback.triple_preimage f U V r hr i j k) (z (r i) (r j) (r k))).symm

end Construction.ModuleCechNaturality

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechSections
