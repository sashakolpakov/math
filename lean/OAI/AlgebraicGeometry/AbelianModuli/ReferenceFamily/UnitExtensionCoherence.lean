import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiniteFreeLocalFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentScalarAlgebraization

/-! # Unit Extension Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitExtensionCoherence

noncomputable section

/-! Every actual extension of the structure module by itself has finite
free algebraic local frames. Native holomorphic splitting is therefore
reflected algebraically without a supplied coherence hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem unitExtension_coherent {X : Scheme.{0}} (M : X.Modules)
    (i : HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (p : M ⟶ HilbertConstruction.Line.Bundles.structureModule X) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact) : M.IsQuasicoherent ∧ M.IsFiniteType := by
  have h := fun x : X => FiniteFreeLocalFrames.unitQuotientExtension_locally_split i p hip hS x
  choose U hx hsplit using h
  let split x := Classical.choice (hsplit x)
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let e x : SheafOfModules.free (R := X.ringCatSheaf.over (U x)) (PUnit ⊕ PUnit) ≅ M.over (U x) :=
    FiniteFreeLocalFrames.structureBinaryFreeIso (U x) ≪≫ (split x).isoBinaryBiproduct.symm
  exact FiniteFreeLocalFrames.finiteFreeFrameData_coherent M U hU (PUnit ⊕ PUnit) e

theorem native_unitExtension_splitting_algebraic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (M : V.carrier.Modules)
    (i : HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ M) (p : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier)
    (hip : i ≫ p = 0) (hS : (ShortComplex.mk i p hip).ShortExact)
    (r : (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj M ⟶
      (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj (HilbertConstruction.Line.Bundles.structureModule V.carrier))
    (hr : (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).map i ≫ r = 𝟙 _) :
    Nonempty (ShortComplex.mk i p hip).Splitting := by
  have h := unitExtension_coherent M i p hip hS
  let : M.IsQuasicoherent := h.1
  let : M.IsFiniteType := h.2
  exact CoherentScalarAlgebraization.native_split_extension_algebraic V M (HilbertConstruction.Line.Bundles.structureModule V.carrier) i p hip hS r hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitExtensionCoherence
