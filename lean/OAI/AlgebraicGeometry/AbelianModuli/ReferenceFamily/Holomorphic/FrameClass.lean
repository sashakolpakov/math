import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass

/-! # Frame Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FrameClass

noncomputable section

section

/-! Arbitrary actual algebraic frames compute the native holomorphic
unit class. The proof uses regular frame changes and common refinements. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {B : V.carrier.Modules}

def frameHolomorphicUnit (r s : LineFrameAtlas.LocalLineFrame B) :
    (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := ↥(AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s)))ˣ :=
  Units.map (DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V (r.domain ⊓ s.domain)).toMonoidHom
    (r.transition s _ inf_le_left inf_le_right)

theorem frameHolomorphicUnit_value (r s : LineFrameAtlas.LocalLineFrame B)
    (x : ↥(AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s)) :
    (frameHolomorphicUnit V r s).val x = AnalyticFrameTransitions.frameTransitionPair V.presentation r s x := rfl

theorem frameUnitCech_class_parent_independent {I : Type}
    (U : I → Opens V.analyticSpace) (hU : ∀ x, ∃ i, x ∈ U i)
    (r s : I → LineFrameAtlas.LocalLineFrame B)
    (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (r i))
    (hs : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (s i))
    (k k' : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1 k = 0)
    (hk' : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1 k' = 0)
    (he : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      (LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x =
        AnalyticFrameTransitions.framePointTransition V.presentation (r (a 0)) (r (a 1)) x.val
          (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
          (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)))
    (he' : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      (LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a)).val x =
        AnalyticFrameTransitions.framePointTransition V.presentation (s (a 0)) (s (a 1)) x.val
          (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
          (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property))) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of V.analyticSpace) U
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace)
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of V.analyticSpace) U hU) 0 k' hk' =
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of V.analyticSpace) U
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace)
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of V.analyticSpace) U hU) 0 k hk := by
  let g (i : I) : (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := U i))ˣ :=
    Units.map (DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (E := V.analyticModel) (le_inf (hr i) (hs i))).toMonoidHom
      (frameHolomorphicUnit V (r i) (s i))
  apply GlobalGluing.holomorphicUnitCech_gauge_class V.analyticModel V.analyticSpace U hU k k' hk hk' g
  intro a x
  rw [he, he']
  exact AnalyticFrameTransitions.framePointTransition_gauge V.presentation (r (a 0)) (r (a 1)) (s (a 0)) (s (a 1)) x.val
    (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
    (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property))
    (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
    (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property))

theorem holomorphicUnitCech_refinement_value {I J : Type}
    (U : I → Opens V.analyticSpace) (W : J → Opens V.analyticSpace)
    (r : J → I) (hr : ∀ j, W j ≤ U (r j))
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1)
    (a : Fin 2 → J) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W a) :
    (LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W a)
      (DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap (X := TopCat.of V.analyticSpace) U W r hr
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj 1 k a)).val x =
      (LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a)) (k (r ∘ a))).val
        ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le U W r hr a x.property⟩ := rfl

end

/-! The holomorphic class of genuine algebraic frame units is unchanged
on an arbitrary common refinement of their covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {B : V.carrier.Modules}

theorem frameUnitCech_class_cover_independent {I J : Type}
    (U : I → Opens V.analyticSpace) (hU : ∀ x, ∃ i, x ∈ U i)
    (W : J → Opens V.analyticSpace) (hW : ∀ x, ∃ j, x ∈ W j)
    (r : I → LineFrameAtlas.LocalLineFrame B) (s : J → LineFrameAtlas.LocalLineFrame B)
    (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (r i))
    (hs : ∀ j, W j ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (s j))
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1)
    (k' : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj W 1)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1 k = 0)
    (hk' : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj W 1 k' = 0)
    (he : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      (LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x =
        AnalyticFrameTransitions.framePointTransition V.presentation (r (a 0)) (r (a 1)) x.val
          (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
          (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)))
    (he' : ∀ (a : Fin 2 → J) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W a),
      (LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W a) (k' a)).val x =
        AnalyticFrameTransitions.framePointTransition V.presentation (s (a 0)) (s (a 1)) x.val
          (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le W a 0 x.property))
          (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le W a 1 x.property))) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of V.analyticSpace) W
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace)
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of V.analyticSpace) W hW) 0 k' hk' =
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of V.analyticSpace) U
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace)
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of V.analyticSpace) U hU) 0 k hk := by
  let T := TopCat.of V.analyticSpace
  let G := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace
  let Z : I × J → Opens V.analyticSpace := fun a => U a.1 ⊓ W a.2
  have hZ : ∀ x, ∃ a, x ∈ Z a := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨j, hj⟩ := hW x
    exact ⟨(i, j), hi, hj⟩
  have hZU : ∀ a, Z a ≤ U a.1 := fun _ => inf_le_left
  have hZW : ∀ a, Z a ≤ W a.2 := fun _ => inf_le_right
  let l := DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap (X := T) U Z Prod.fst hZU G.obj 1 k
  let l' := DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap (X := T) W Z Prod.snd hZW G.obj 1 k'
  have hl := DivisorClass.Chern.Cech.ClassRefinement.abelianCechRefinementMap_closed (X := T) U Z Prod.fst hZU G.obj 1 k hk
  have hl' := DivisorClass.Chern.Cech.ClassRefinement.abelianCechRefinementMap_closed (X := T) W Z Prod.snd hZW G.obj 1 k' hk'
  have hc : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := T) Z G (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) Z hZ) 0 l' hl' =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := T) Z G (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) Z hZ) 0 l hl := by
    apply frameUnitCech_class_parent_independent V Z hZ (r ∘ Prod.fst) (s ∘ Prod.snd)
      (fun a => (hZU a).trans (hr a.1)) (fun a => (hZW a).trans (hs a.2)) l l' hl hl'
    · intro a x
      exact (holomorphicUnitCech_refinement_value V U Z Prod.fst hZU k a x).trans
        (he (Prod.fst ∘ a) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le U Z Prod.fst hZU a x.property⟩)
    · intro a x
      exact (holomorphicUnitCech_refinement_value V W Z Prod.snd hZW k' a x).trans
        (he' (Prod.snd ∘ a) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le W Z Prod.snd hZW a x.property⟩)
  exact (DivisorClass.Chern.Cech.ClassRefinement.abelianCechSheafClass_refinement (X := T) W Z Prod.snd hZW G
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) W hW) (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) Z hZ) 0 k' hk').symm.trans
      (hc.trans (DivisorClass.Chern.Cech.ClassRefinement.abelianCechSheafClass_refinement (X := T) U Z Prod.fst hZU G
        (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) U hU) (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) Z hZ) 0 k hk))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FrameClass
