import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass
import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalFrame

/-! # Holomorphic Trivial Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTrivialClass

noncomputable section

/-! An actual global algebraic frame gives the constructed native
holomorphic trivialization. The identity of the algebraic Picard group
therefore maps to the identity of holomorphic unit cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
  (e : L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule V.carrier)

local instance trivialHolomorphicClassGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of V.analyticSpace)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace) 1

def nativeGlobalFrameHolomorphicUnit (i : V.carrier) :
    (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := (ChernClasses.nativeLineBundle V.presentation L).analyticCover i))ˣ :=
  Units.map (DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V
    ((ChernClasses.nativeLineBundle V.presentation L).trivializingOpen i)).toMonoidHom
    ((ChernClasses.nativeLineBundle V.presentation L).globalFrameUnit e i _ le_rfl)

include e in
theorem nativeHolomorphicTrivialization_of_globalFrame : HolomorphicIsoClass.NativeHolomorphicTrivialization V L := by
  let B := ChernClasses.nativeLineBundle V.presentation L
  let g (i : B.LogCoverIndex) : (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := B.logCover i))ˣ :=
    Units.map (DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (E := V.analyticModel) (M := V.analyticSpace)
      (B.logCover_subset i)).toMonoidHom (nativeGlobalFrameHolomorphicUnit V L e (B.logParent i))
  refine ⟨g, ?_⟩
  intro a x
  exact B.pointTransition_global_ratio e (B.logParent (a 0)) (B.logParent (a 1)) x.val
    (B.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le B.logCover a 0 x.property))
    (B.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le B.logCover a 1 x.property))

include e in
theorem nativeHolomorphicLineClass_of_globalFrame : HolomorphicLineClass.nativeHolomorphicLineClass V L = 0 :=
  (HolomorphicIsoClass.nativeHolomorphicLineClass_eq_zero_iff V L).mpr (nativeHolomorphicTrivialization_of_globalFrame V L e)

theorem nativeHolomorphicPicardClass_one : HolomorphicIsoClass.nativeHolomorphicPicardClass V 1 = 0 :=
  nativeHolomorphicLineClass_of_globalFrame V (HilbertConstruction.Line.Bundles.LineBundle.trivial V.carrier) (Iso.refl _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTrivialClass
