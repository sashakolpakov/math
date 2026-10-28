import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UnitEndPullback
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleIso
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Unit End Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UnitEndIso.Construction

noncomputable section

/-! A structure-sheaf endomorphism is locally invertible exactly where its scalar is a unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIso_pullback_unitEnd_basicOpen (X : Scheme.{u}) (q : End (LineBundle.Construction.structureSheafModule X)) :
    IsIso ((Scheme.Modules.pullback (X.basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv X q)).ι).map q) := by
  apply (UnitEndPullback.Construction.isIso_pullback_unitEnd_iff _ q).mpr
  let U := X.basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv X q)
  have hU : U.ι ''ᵁ ⊤ ≤ U := by simp
  have hu := (X.toRingedSpace.isUnit_res_basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv X q)).map
    (X.presheaf.map (homOfLE hU).op).hom
  change IsUnit (X.presheaf.map (homOfLE hU).op
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (ModuleSections.Construction.structureSheafEndRingEquiv X q))) at hu
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp] at hu
  rw [Scheme.Opens.ι_appTop]
  exact hu

theorem mem_basicOpen_of_isIso_pullback_unitEnd {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : End (LineBundle.Construction.structureSheafModule Y)) [IsIso ((Scheme.Modules.pullback f).map q)] (x : X) :
    f x ∈ Y.basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv Y q) := by
  have hu := (UnitEndPullback.Construction.isIso_pullback_unitEnd_iff f q).mp inferInstance
  have he : f ⁻¹ᵁ Y.basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv Y q) = ⊤ :=
    (f.preimage_basicOpen_top _).trans (X.basicOpen_of_isUnit hu)
  have hx : x ∈ f ⁻¹ᵁ Y.basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv Y q) := by rw [he]; trivial
  exact hx

theorem unitEnd_mem_isoLocus_of_isIso_residueFiber (X : Scheme.{u})
    (q : End (LineBundle.Construction.structureSheafModule X)) (x : X)
    [IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map q)] : x ∈ ModuleIso.Construction.moduleIsoLocus q := by
  apply (ModuleIso.Construction.mem_moduleIsoLocus_iff q x).mpr
  refine ⟨X.basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv X q), ?_, isIso_pullback_unitEnd_basicOpen X q⟩
  have hx := mem_basicOpen_of_isIso_pullback_unitEnd (X.fromSpecResidueField x) q
    (IsLocalRing.closedPoint (X.residueField x))
  exact (congrArg (fun y : X ↦ y ∈ X.basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv X q))
    (X.fromSpecResidueField_apply x (IsLocalRing.closedPoint (X.residueField x)))).mp hx

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UnitEndIso.Construction
