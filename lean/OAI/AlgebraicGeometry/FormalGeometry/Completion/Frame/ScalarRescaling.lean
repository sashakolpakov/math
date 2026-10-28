import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.AxisRigidity

/-! # Scalar Rescaling -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.ScalarRescaling

noncomputable section

/-! Rescaling a frame changes its rigidification value by the actual
pullback of the rescaling function. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

def scalarUnitIso (X : Scheme.{u}) (a : Γ(X, ⊤)ˣ) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X := by
  haveI : IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm a.val) :=
    (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff _).mpr (by
      change IsUnit (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X ((AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm a.val))
      rw [RingEquiv.apply_symm_apply]
      exact a.isUnit)
  exact asIso ((AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm a.val)

theorem scalarUnitIso_value (X : Scheme.{u}) (a : Γ(X, ⊤)ˣ) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (scalarUnitIso X a).hom = a.val :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply a.val

theorem frameAxisScalar_precompIso {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r (a ≪≫ e) =
      b.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue Y a.hom) * Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e := by
  let α : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) := (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).inv ≫
    (Scheme.Modules.pullback b).map a.hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).hom
  let c : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) := (Rigidified.FrameScalar.Construction.frameAxisIso f b g s h M r e).hom
  have he : (Rigidified.FrameScalar.Construction.frameAxisIso f b g s h M r (a ≪≫ e)).hom = α ≫ c := by
    simp only [Rigidified.FrameScalar.Construction.frameAxisIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.map_comp, α, c, Category.assoc, Iso.hom_inv_id_assoc]
  have hp := Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback b a.hom
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T α = b.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue Y a.hom) at hp
  exact (congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) he).trans
    ((map_mul (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) c α).trans
      ((congrArg (fun z => AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T c * z) hp).trans (mul_comm _ _)))

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.ScalarRescaling
