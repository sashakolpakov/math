import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UnitEndIso
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleIsoNeighborhood
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction

/-! # Line Bundle Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleIso.Construction

noncomputable section

/-! Invertibility on a field-valued fiber detects local invertibility of a line-bundle morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem lineBundle_morphism_image_mem_isoLocus
    {k : Type u} [Field k] {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) (q : M ⟶ N)
    (p : Spec (.of k) ⟶ X) [IsIso ((Scheme.Modules.pullback p).map q)] (t : Spec (.of k)) :
    p t ∈ ModuleIso.Construction.moduleIsoLocus q := by
  obtain ⟨U₁, ht₁, ⟨e₁⟩⟩ := hM (p t)
  obtain ⟨U₂, ht₂, ⟨e₂⟩⟩ := hN (p t)
  let U := U₁ ⊓ U₂
  have htU : p t ∈ U := ⟨ht₁, ht₂⟩
  let eM := TensorRestriction.Construction.restrictLineBundleTrivialization (show U ≤ U₁ from inf_le_left) e₁
  let eN := TensorRestriction.Construction.restrictLineBundleTrivialization (show U ≤ U₂ from inf_le_right) e₂
  have hrange : Set.range p ⊆ Set.range U.ι := by
    rintro x ⟨v, rfl⟩
    have hv : p v ∈ U := by simpa only [Subsingleton.elim v t] using htU
    exact ⟨⟨p v, hv⟩, rfl⟩
  let r : Spec (.of k) ⟶ U.toScheme := IsOpenImmersion.lift U.ι p hrange
  have hr : r ≫ U.ι = p := IsOpenImmersion.lift_fac U.ι p hrange
  have hcomp : IsIso ((Scheme.Modules.pullback (r ≫ U.ι)).map q) :=
    ModuleIso.Construction.isIso_map_of_naturalIso (Scheme.Modules.pullbackCongr hr.symm) q
  have hdouble : IsIso ((Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback r).map q) :=
    ModuleIso.Construction.isIso_map_of_naturalIso (Scheme.Modules.pullbackComp r U.ι).symm q
  have hqU : IsIso ((Scheme.Modules.pullback r).map ((Scheme.Modules.pullback U.ι).map q)) := hdouble
  let qU : End (LineBundle.Construction.structureSheafModule U.toScheme) := eM.inv ≫ (Scheme.Modules.pullback U.ι).map q ≫ eN.hom
  have hqU' : IsIso ((Scheme.Modules.pullback r).map qU) := by
    dsimp only [qU]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  have hxU : r t ∈ ModuleIso.Construction.moduleIsoLocus qU := (ModuleIso.Construction.mem_moduleIsoLocus_iff qU (r t)).mpr
    ⟨U.toScheme.basicOpen (ModuleSections.Construction.structureSheafEndRingEquiv U.toScheme qU),
      UnitEndIso.Construction.mem_basicOpen_of_isIso_pullback_unitEnd r qU t, UnitEndIso.Construction.isIso_pullback_unitEnd_basicOpen U.toScheme qU⟩
  have hx := ModuleIsoNeighborhood.Construction.image_mem_moduleIsoLocus U.ι q (r t)
    (ModuleIsoNeighborhood.Construction.mem_moduleIsoLocus_of_conjugate ((Scheme.Modules.pullback U.ι).map q) eM.symm eN (r t) hxU)
  exact (congrArg (fun y : X ↦ y ∈ ModuleIso.Construction.moduleIsoLocus q)
    (congrArg (fun a : Spec (.of k) ⟶ X ↦ a t) hr)).mp hx

theorem lineBundle_morphism_mem_isoLocus_iff
    {X : Scheme.{u}} {M N : X.Modules} (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N)
    (q : M ⟶ N) (x : X) :
    x ∈ ModuleIso.Construction.moduleIsoLocus q ↔ IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map q) := by
  constructor
  · intro hx
    obtain ⟨U, hxU, hU⟩ := (ModuleIso.Construction.mem_moduleIsoLocus_iff q x).mp hx
    have hrange : Set.range (X.fromSpecResidueField x) ⊆ Set.range U.ι := by
      rintro y ⟨v, rfl⟩
      exact ⟨⟨x, hxU⟩, (X.fromSpecResidueField_apply x v).symm⟩
    let r := IsOpenImmersion.lift U.ι (X.fromSpecResidueField x) hrange
    have hcomp := @ModuleIso.Construction.isIso_pullbackMap_comp X U.toScheme (Spec (X.residueField x)) U.ι r M N q hU
    exact ModuleIso.Construction.isIso_map_of_naturalIso
      (Scheme.Modules.pullbackCongr (IsOpenImmersion.lift_fac U.ι (X.fromSpecResidueField x) hrange)) q
  · intro hq
    have hx := @lineBundle_morphism_image_mem_isoLocus (X.residueField x) _ X M N hM hN q
      (X.fromSpecResidueField x) hq (IsLocalRing.closedPoint (X.residueField x))
    exact (congrArg (fun y : X ↦ y ∈ ModuleIso.Construction.moduleIsoLocus q)
      (X.fromSpecResidueField_apply x (IsLocalRing.closedPoint (X.residueField x)))).mp hx

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleIso.Construction
