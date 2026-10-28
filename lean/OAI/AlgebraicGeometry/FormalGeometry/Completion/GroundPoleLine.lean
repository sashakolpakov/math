import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleLine
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundDenominator

/-! # Ground Pole Line -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundPoleLine.Construction.GroundPoleLineBundle

noncomputable section

/-! The pole line bundle and its canonical section over the actual ground field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle

variable {X : Scheme.{u}} [IsIntegral X]

def lineBundle {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f] (r : X.functionField) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := Quotients.FiniteDescent.FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf (Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle.stalkModules r)
  locallyTrivial x := by
    obtain ⟨U, hxU, a, ha⟩ := GroundDenominator.Construction.GroundDenominatorNeighborhood.exists_principal f r x
    have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    change (Quotients.FiniteDescent.DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a} at ha
    have hne : (X.germToFunctionField U.1 a)⁻¹ ≠ 0 := inv_ne_zero (by
      simpa only [map_zero] using (X.germToFunctionField_injective U.1).ne
        (Quotients.FiniteDescent.DenominatorLine.Construction.DenominatorLineBundle.generator_ne_zero r U a ha))
    have hmem (y : U.1) : (X.germToFunctionField U.1 a)⁻¹ ∈ Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle.stalkModules r y := by
      rw [Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle.generator r U a ha y]
      exact Submodule.mem_span_singleton_self _
    exact ⟨U.1, hxU, ⟨Quotients.FiniteDescent.FractionalIdealFrame.Construction.FractionalIdealFrames.frameIso (Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle.stalkModules r) U.1 _ hmem hne
      (Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle.generator r U a ha)⟩⟩

def canonicalSection {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f] (r : X.functionField) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (lineBundle f r).sheaf where
  val.app U := ModuleCat.ofHom (R := Γ(X, U.unop)) (X := Γ(X, U.unop))
    (Y := Γ(Quotients.FiniteDescent.FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf (Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle.stalkModules r), U.unop))
    (Quotients.FiniteDescent.FractionalIdealFrame.Construction.FractionalIdealFrames.multiply (Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle.stalkModules r) (show U.unop ≤ ⊤ from le_top) 1
      (fun x => Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal.one_mem _))
  val.naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change Γ(X, U.unop) at s
    exact (Quotients.FiniteDescent.FractionalIdealFrame.Construction.FractionalIdealFrames.multiply_natural (Quotients.FiniteDescent.PoleLine.Construction.PoleLineBundle.stalkModules r)
      (show U.unop ≤ ⊤ from le_top) h.unop.le 1 (fun x => Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal.one_mem _) s).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundPoleLine.Construction.GroundPoleLineBundle
