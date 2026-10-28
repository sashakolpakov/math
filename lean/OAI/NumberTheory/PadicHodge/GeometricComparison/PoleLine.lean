import OAI.NumberTheory.PadicHodge.GeometricComparison.DenominatorNeighborhoodLe
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorLine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealFrame
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq

/-! # Pole Line -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PoleLine.PoleLineBundle

noncomputable section

/-! Pole line bundles over arbitrary fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X]

def stalkModules (r : X.functionField) (x : X) :
    Submodule (X.presheaf.stalk x) X.functionField :=
  AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal.module (AlgebraicGeometry.Quotients.FiniteDescent.DenominatorLine.Construction.DenominatorLineBundle.stalkIdeals r x)

theorem generator (r : X.functionField) (U : X.affineOpens) [Nonempty U.1]
    (a : Γ(X, U)) (ha : (AlgebraicGeometry.Quotients.FiniteDescent.DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a}) (x : U.1) :
    stalkModules r x = Submodule.span (X.presheaf.stalk x) {(X.germToFunctionField U.1 a)⁻¹} := by
  have hne : X.germToFunctionField U.1 a ≠ 0 := by
    simpa only [map_zero] using (X.germToFunctionField_injective U.1).ne
      (AlgebraicGeometry.Quotients.FiniteDescent.DenominatorLine.Construction.DenominatorLineBundle.generator_ne_zero r U a ha)
  change AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal.module (AlgebraicGeometry.Quotients.FiniteDescent.DenominatorLine.Construction.DenominatorLineBundle.stalkIdeals r x) = _
  rw [AlgebraicGeometry.Quotients.FiniteDescent.DenominatorLine.Construction.DenominatorLineBundle.stalk_generator r U a ha x]
  have hne' : algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ U.1 x x.2 a) ≠ 0 := by
    rwa [X.algebraMap_germ_eq_germToFunctionField]
  rw [AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal.span_eq _ hne', X.algebraMap_germ_eq_germToFunctionField]

def lineBundle {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f] (r : X.functionField) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf (stalkModules r)
  locallyTrivial x := by
    obtain ⟨U, hxU, a, ha⟩ := DenominatorNeighborhoodLe.DenominatorNeighborhood.exists_principal f r x
    have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    change (AlgebraicGeometry.Quotients.FiniteDescent.DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a} at ha
    have hne : (X.germToFunctionField U.1 a)⁻¹ ≠ 0 := inv_ne_zero (by
      simpa only [map_zero] using (X.germToFunctionField_injective U.1).ne
        (AlgebraicGeometry.Quotients.FiniteDescent.DenominatorLine.Construction.DenominatorLineBundle.generator_ne_zero r U a ha))
    have hmem (y : U.1) : (X.germToFunctionField U.1 a)⁻¹ ∈ stalkModules r y := by
      rw [generator r U a ha y]
      exact Submodule.mem_span_singleton_self _
    exact ⟨U.1, hxU, ⟨AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealFrame.Construction.FractionalIdealFrames.frameIso (stalkModules r) U.1 _ hmem hne
      (generator r U a ha)⟩⟩

def canonicalSection {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f] (r : X.functionField) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (lineBundle f r).sheaf where
  val.app U := ModuleCat.ofHom (R := Γ(X, U.unop)) (X := Γ(X, U.unop))
    (Y := Γ(AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealIs.Construction.FractionalIdealSheaf.sheaf (stalkModules r), U.unop))
    (AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealFrame.Construction.FractionalIdealFrames.multiply (stalkModules r) (show U.unop ≤ ⊤ from le_top) 1
      (fun x => AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal.one_mem _))
  val.naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change Γ(X, U.unop) at s
    exact (AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealFrame.Construction.FractionalIdealFrames.multiply_natural (stalkModules r)
      (show U.unop ≤ ⊤ from le_top) h.unop.le 1 (fun x => AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal.one_mem _) s).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PoleLine.PoleLineBundle
