import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.Presentations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Quasicoherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
The concrete locally trivial sheaves defining HilbertConstruction line bundles are finitely
presented and quasi-coherent. Their pullback frames are transported to the
slice-site presentations used by mathlib.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)

/-- A frame on an open subscheme gives a frame on the equivalent slice site. -/
def Line.Bundles.LineBundle.overFrameIso (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L.sheaf ≅ Line.Bundles.structureModule U.toScheme) :
    L.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso <|
    (Scheme.Modules.overFunctorEquiv U).app L.sheaf ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf ≪≫ e ≪≫
    (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv U).app (Line.Bundles.structureModule X)).symm

/-- Local frames supply actual presentations with one generator and no relations. -/
def Line.Bundles.LineBundle.localPresentationData : L.sheaf.QuasicoherentData where
  I := X
  X x := (L.locallyTrivial x).choose
  coversTop := by
    rw [Opens.coversTop_iff, IsOpenCover]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, (L.locallyTrivial x).choose_spec.1⟩
  presentation x :=
    (Finite.Presentations.unitFinitePresentation _).ofIsIso
      (L.overFrameIso _ (L.locallyTrivial x).choose_spec.2.some).inv

instance Line.Bundles.LineBundle.localPresentationData_isFinite : L.localPresentationData.IsFinitePresentation where
  isFinite_presentation x := by
    change ((Finite.Presentations.unitFinitePresentation _).ofIsIso
      (L.overFrameIso _ (L.locallyTrivial x).choose_spec.2.some).inv).IsFinite
    infer_instance

/-- Every line bundle in the concrete HilbertConstruction API is finitely presented. -/
instance Line.Bundles.LineBundle.isFinitePresentation : L.sheaf.IsFinitePresentation where
  exists_quasicoherentData := ⟨L.localPresentationData, inferInstance⟩

/-- In particular, line bundles satisfy the usual quasi-coherence condition. -/
theorem Line.Bundles.LineBundle.isQuasicoherent : L.sheaf.IsQuasicoherent :=
  L.localPresentationData.isQuasicoherent

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
