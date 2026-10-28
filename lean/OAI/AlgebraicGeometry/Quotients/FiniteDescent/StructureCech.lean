import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechPullbackShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoefficient
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructureSections

/-! # Structure Cech -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructureCech

noncomputable section

/-! The ordinary structure-sheaf Cech pullback, normalized to regular
functions on the source scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.StructureCechPullback

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechPullbackShort.Construction.ModuleCechPullback

variable {X Y S : Scheme.{u}}
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S) (h : f ≫ π = ρ)
    {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)
    (r : κ → ι) (hr : ∀ j, V j ≤ f ⁻¹ᵁ U (r j))

def map : OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex (BaseModule.Construction.BaseModuleSheaf.sheaf π (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) U ⟶
    OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex (BaseModule.Construction.BaseModuleSheaf.sheaf ρ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) V :=
  ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ h (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U V r hr ≫
    (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor ρ V).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom

theorem middle_apply
    (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (BaseModule.Construction.BaseModuleSheaf.sheaf π (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) U) (i j : κ) :
    (StructureCechPullback.map f π ρ h U V r hr).τ₂ z i j =
      f.appLE (U (r i) ⊓ U (r j)) (V i ⊓ V j)
        (ModuleCechD.Construction.ModuleCechPullback.cechPullback_overlap_preimage f U V r hr i j) (z (r i) (r j)) :=
  StructureSections.Construction.StructureSectionsOver.apply f π ρ h _ _ _ _

end Construction.StructureCechPullback

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructureCech
