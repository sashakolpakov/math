import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructureCech

/-! # Module Cech Axis -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechAxis

noncomputable section

/-! Trivializing a bundle before or after geometric Cech restriction gives
the same map to the structure-sheaf complex. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ModuleCechNormalization

variable {X Y S : Scheme.{u}}
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S) (h : f ≫ π = ρ)
    {M : X.Modules} (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)
    (r : κ → ι) (hr : ∀ j, V j ≤ f ⁻¹ᵁ U (r j))

def axisIso :
    (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor ρ V).obj ((Scheme.Modules.pullback f).obj M) ≅
      (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor ρ V).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :=
  (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor ρ V).mapIso
    ((Scheme.Modules.pullback f).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f)

theorem square : ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ h M U V r hr ≫ (axisIso f ρ e V).hom =
    ((CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor π U).mapIso e).hom ≫
      StructureCech.Construction.StructureCechPullback.map f π ρ h U V r hr := by
  change ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ h M U V r hr ≫
    (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor ρ V).map
      ((Scheme.Modules.pullback f).map e.hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom) = _
  rw [Functor.map_comp, ← Category.assoc, ModuleCechSections.Construction.ModuleCechNaturality.shortMap, Category.assoc]
  rfl

end Construction.ModuleCechNormalization

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechAxis
