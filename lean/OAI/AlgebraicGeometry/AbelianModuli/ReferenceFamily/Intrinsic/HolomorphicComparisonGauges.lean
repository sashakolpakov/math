import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameUnitCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass

/-! # Holomorphic Comparison Gauges -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicComparisonGauges

noncomputable section

/-! Equality of original native holomorphic line classes produces
actual nowhere-vanishing holomorphic comparison gauges on any common
cover carrying algebraic frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance holomorphicComparisonGauges_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of V.analyticSpace)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace) 1

theorem exists_nativeHolomorphicComparisonGauges (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    (he : HolomorphicLineClass.nativeHolomorphicLineClass V L = HolomorphicLineClass.nativeHolomorphicLineClass V K)
    {I : Type} (U : I → Opens V.analyticSpace) (hU : ∀ x, ∃ i, x ∈ U i)
    (r : I → LineFrameAtlas.LocalLineFrame L.sheaf) (s : I → LineFrameAtlas.LocalLineFrame K.sheaf)
    (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (r i))
    (hs : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (s i)) :
    ∃ g : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := U i))ˣ,
      ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
        AnalyticFrameTransitions.framePointTransition V.presentation (r (a 0)) (r (a 1)) x.val
          (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
          (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)) /
        AnalyticFrameTransitions.framePointTransition V.presentation (s (a 0)) (s (a 1)) x.val
          (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
          (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)) =
          (g (a 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
            (g (a 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩ := by
  let T := TopCat.of V.analyticSpace
  let S := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace
  let : AddCommGroup (CategoryTheory.Sheaf.H S 1) := Cech.Add.cechClassAddCommGroup (X := T) S 1
  let k := FrameUnitCocycle.frameUnitCech V U r hr
  let l := FrameUnitCocycle.frameUnitCech V U s hs
  have hk := FrameUnitCocycle.frameUnitCech_closed V U r hr
  have hl := FrameUnitCocycle.frameUnitCech_closed V U s hs
  have hsub := Cech.Add.cechSub_closed (X := T) U S.obj 1 k l hk hl
  have hz : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := T) U S (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) U hU) 0
      (k - l) hsub = 0 := by
    have hc := Cech.Add.cechSheafClass_sub (X := T) U S (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) U hU) 0 k l hk hl
    have hL := FrameUnitCocycle.nativeHolomorphicLineClass_frameUnits V U L r hr hU
    have hK := FrameUnitCocycle.nativeHolomorphicLineClass_frameUnits V U K s hs hU
    exact hc.trans ((congrArg₂ (fun x y : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace => x - y)
      hL.symm hK.symm).trans (sub_eq_zero.mpr he))
  obtain ⟨g, hg⟩ := HolomorphicIsoClass.holomorphicUnitCech_trivialization_of_class_zero V.analyticModel V.analyticSpace
    U hU (k - l) hsub hz
  refine ⟨g, ?_⟩
  intro a x
  have h := hg a x
  change (Holomorphic.LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
    (k a - l a)).val x = _ at h
  rw [Holomorphic.LogUnitClass.holomorphicUnitSection_value_sub] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicComparisonGauges
