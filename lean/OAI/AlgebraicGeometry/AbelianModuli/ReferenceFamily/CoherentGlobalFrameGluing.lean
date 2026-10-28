import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameOverComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TransitionGaugeGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.LineFrameOverTransitions

/-! # Coherent Global Frame Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentGlobalFrameGluing

noncomputable section

/-! Actual local line frames with transition unit one glue to an
original global frame whose native restriction equals each given frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

local instance coherentFrameMulCommutative (X : Scheme.{0}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm (fun a b => mul_comm a b)

theorem nativeOverFrame_injective {X : Scheme.{0}} (M : X.Modules) (U : X.Opens) :
    Function.Injective (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U) := by
  intro e f h
  exact (SheafCohomology.Projective.OpenFrames.restrictTrivializationOfOverTrivializationOfRestrictIso M U e).symm.trans
    ((congrArg (SheafCohomology.Projective.FrameSections.restrictTrivializationOfOverIso M U) h).trans
      (SheafCohomology.Projective.OpenFrames.restrictTrivializationOfOverTrivializationOfRestrictIso M U f))

theorem globalOpenFrame_refl {X : Scheme.{0}} (U : X.Opens) :
    Global.FrameOverComparison.globalOpenFrame (Iso.refl (HilbertConstruction.Line.Bundles.structureModule X)) U = Scheme.Modules.restrictUnitIso U.ι := by
  exact (congrArg (fun e => e ≪≫ Scheme.Modules.restrictUnitIso U.ι)
    ((Scheme.Modules.restrictFunctor U.ι).mapIso_refl (HilbertConstruction.Line.Bundles.structureModule X))).trans (Iso.refl_trans _)

theorem framedUnitIso_one {X : Scheme.{0}} (M N : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (g : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (RepresentationTheory.Theta.Geometric.FramedUnitIsomorphisms.framedUnitIso M N U e g 1).hom = e.hom ≫ g.inv := by
  have hu : SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U 1 = 𝟙 _ :=
    (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEndRingHom X.ringCatSheaf U).map_one
  change e.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U 1 ≫ g.inv = _
  rw [hu, Category.id_comp]

theorem exists_global_frame_agreeing {X : Scheme.{0}} {M : X.Modules} {I : Type}
    (s : I → LineFrameAtlas.LocalLineFrame M) (hs : iSup (fun i => (s i).domain) = ⊤)
    (htrans : ∀ i j, (s i).transition (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right = 1) :
    ∃ e : M ≅ HilbertConstruction.Line.Bundles.structureModule X, ∀ i, Global.FrameOverComparison.globalOpenFrame e (s i).domain = (s i).frame := by
  let U := fun i => (s i).domain
  let t := fun i => Global.FrameTransitions.localFrameOfGlobal (Iso.refl (HilbertConstruction.Line.Bundles.structureModule X)) (U i)
  let a := fun i j => (s i).transition (s j) (U i ⊓ U j) inf_le_left inf_le_right |>.val
  let b := fun i j => (t i).transition (t j) (U i ⊓ U j) inf_le_left inf_le_right |>.val
  let e := fun i => SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M (U i) (s i).frame
  let g := fun i => SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso (HilbertConstruction.Line.Bundles.structureModule X) (U i) (t i).frame
  have he (i j : I) := Local.LineFrameOverTransitions.localLineFrame_over_transition (s i) (s j) (U i ⊓ U j) inf_le_left inf_le_right
  have hg (i j : I) := Local.LineFrameOverTransitions.localLineFrame_over_transition (t i) (t j) (U i ⊓ U j) inf_le_left inf_le_right
  have hr (i j : I) : a i j *
      (RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit (show U i ⊓ U j ≤ U i from inf_le_left) (1 : Γ(X, U i)ˣ)).val =
      (RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit (show U i ⊓ U j ≤ U j from inf_le_right) (1 : Γ(X, U j)ˣ)).val * b i j := by
    have ha : a i j = 1 := congrArg Units.val (htrans i j)
    have hb : b i j = 1 := congrArg Units.val
      (Global.FrameTransitions.localFrameOfGlobal_transition (Iso.refl (HilbertConstruction.Line.Bundles.structureModule X)) (U i) (U j) (U i ⊓ U j) inf_le_left inf_le_right)
    change a i j * X.presheaf.map _ 1 = X.presheaf.map _ 1 * b i j
    rw [ha, hb, map_one, map_one]
  obtain ⟨f, hf⟩ := RepresentationTheory.Theta.Geometric.FramedUnitGluing.exists_iso_of_framed_units M (HilbertConstruction.Line.Bundles.structureModule X) U hs e g (fun _ => 1) a b he hg hr
  refine ⟨f, fun i => ?_⟩
  apply nativeOverFrame_injective M (U i)
  have hu : SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso (HilbertConstruction.Line.Bundles.structureModule X) (U i)
      (Scheme.Modules.restrictUnitIso (U i).ι) = g i :=
    congrArg (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso (HilbertConstruction.Line.Bundles.structureModule X) (U i)) (globalOpenFrame_refl (U i)).symm
  have h := congrArg (fun z => z ≫ (g i).hom) ((hf i).trans (framedUnitIso_one M (HilbertConstruction.Line.Bundles.structureModule X) (U i) (e i) (g i)))
  have hc : ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).mapIso f ≪≫ g i) = e i := by
    apply Iso.ext
    exact h.trans (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact (Global.FrameOverComparison.globalOpenFrame_over f (U i)).trans
    ((congrArg ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).mapIso f ≪≫ ·) hu).trans hc)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentGlobalFrameGluing
