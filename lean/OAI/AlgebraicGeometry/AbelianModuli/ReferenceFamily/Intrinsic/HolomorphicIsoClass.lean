import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicChernComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing

/-! # Holomorphic Iso Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass

noncomputable section

section

/-! Actual algebraic sheaf isomorphisms preserve the constructed native
holomorphic unit class. The comparison uses their regular mixed frame
units on a common refinement. Thus the construction descends to the
actual algebraic Picard group of line-bundle isomorphism classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
  (e : L.sheaf ≅ K.sheaf)

def nativeMixedHolomorphicUnit (i j : V.carrier) :
    (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := ↥((ChernClasses.nativeLineBundle V.presentation L).analyticCover i ⊓
        (ChernClasses.nativeLineBundle V.presentation K).analyticCover j)))ˣ :=
  Units.map (DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V
    ((ChernClasses.nativeLineBundle V.presentation L).trivializingOpen i ⊓
      (ChernClasses.nativeLineBundle V.presentation K).trivializingOpen j)).toMonoidHom
    ((ChernClasses.nativeLineBundle V.presentation L).mixedTransitionOn (ChernClasses.nativeLineBundle V.presentation K) e
      i j _ inf_le_left inf_le_right)

theorem nativeMixedHolomorphicUnit_value (i j : V.carrier)
    (x : ↥((ChernClasses.nativeLineBundle V.presentation L).analyticCover i ⊓
      (ChernClasses.nativeLineBundle V.presentation K).analyticCover j)) :
    (nativeMixedHolomorphicUnit V L K e i j).val x =
      (ChernClasses.nativeLineBundle V.presentation L).mixedTransitionPair (ChernClasses.nativeLineBundle V.presentation K) e i j x := rfl

include e in
theorem nativeHolomorphicClass_iso_on_cover {I : Type}
    (U : I → Opens V.analyticSpace) (hU : ∀ x, ∃ i, x ∈ U i)
    (r s : I → V.carrier)
    (hr : ∀ i, U i ≤ (ChernClasses.nativeLineBundle V.presentation L).analyticCover (r i))
    (hs : ∀ i, U i ≤ (ChernClasses.nativeLineBundle V.presentation K).analyticCover (s i))
    (l k : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of V.analyticSpace) U)
    (hl : ∀ a, ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ) ∞ (l a))
    (hk : ∀ a, ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ) ∞ (k a))
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of V.analyticSpace) U l)
    (h' : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of V.analyticSpace) U k)
    (he : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a x) = (ChernClasses.nativeLineBundle V.presentation L).pointTransition (r (a 0)) (r (a 1)) x.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)))
    (he' : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (k a x) = (ChernClasses.nativeLineBundle V.presentation K).pointTransition (s (a 0)) (s (a 1)) x.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property))) :
    Holomorphic.LogUnitClass.holomorphicLogUnitClass V.analyticModel V.analyticSpace U k hk h' hU =
      Holomorphic.LogUnitClass.holomorphicLogUnitClass V.analyticModel V.analyticSpace U l hl h hU := by
  let g (i : I) : (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := U i))ˣ :=
    Units.map (DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (E := V.analyticModel)
      (le_inf (hr i) (hs i))).toMonoidHom (nativeMixedHolomorphicUnit V L K e (r i) (s i))
  apply Holomorphic.GlobalGluing.holomorphicLogUnitClass_gauge V.analyticModel V.analyticSpace U hU l k hl hk h h' g
  intro a x
  rw [he, he']
  exact (ChernClasses.nativeLineBundle V.presentation L).mixedPointTransition_gauge
    (ChernClasses.nativeLineBundle V.presentation K) e (r (a 0)) (r (a 1)) (s (a 0)) (s (a 1)) x.val
    (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
    (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property))
    (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
    (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property))

include e in
theorem nativeHolomorphicLineClass_iso : HolomorphicLineClass.nativeHolomorphicLineClass V L = HolomorphicLineClass.nativeHolomorphicLineClass V K := by
  let B := ChernClasses.nativeLineBundle V.presentation L
  let C := ChernClasses.nativeLineBundle V.presentation K
  let T := TopCat.of V.analyticSpace
  let W : B.LogCoverIndex × C.LogCoverIndex → Opens V.analyticSpace :=
    fun a => B.logCover a.1 ⊓ C.logCover a.2
  have hW : ∀ x, ∃ a, x ∈ W a := by
    intro x
    obtain ⟨i, hi⟩ := B.logCover_covers x
    obtain ⟨j, hj⟩ := C.logCover_covers x
    exact ⟨(i, j), hi, hj⟩
  have hWL : ∀ a, W a ≤ B.logCover a.1 := fun _ => inf_le_left
  have hWK : ∀ a, W a ≤ C.logCover a.2 := fun _ => inf_le_right
  let l := DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech T B.logCover W Prod.fst hWL B.bundleLogCech
  let k := DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech T C.logCover W Prod.snd hWK C.bundleLogCech
  have hl := Holomorphic.LogClassComparison.holomorphic_refineLogCech V.analyticModel V.analyticSpace B.logCover W Prod.fst hWL
    B.bundleLogCech (HolomorphicLineClass.nativeBundleLogCech_holomorphic V L)
  have hk := Holomorphic.LogClassComparison.holomorphic_refineLogCech V.analyticModel V.analyticSpace C.logCover W Prod.snd hWK
    C.bundleLogCech (HolomorphicLineClass.nativeBundleLogCech_holomorphic V K)
  have h := DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement T B.logCover W Prod.fst hWL B.bundleLogCech B.bundleLogCech_cocycle
  have h' := DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement T C.logCover W Prod.snd hWK C.bundleLogCech C.bundleLogCech_cocycle
  have hc : Holomorphic.LogUnitClass.holomorphicLogUnitClass V.analyticModel V.analyticSpace W k hk h' hW =
      Holomorphic.LogUnitClass.holomorphicLogUnitClass V.analyticModel V.analyticSpace W l hl h hW := by
    apply nativeHolomorphicClass_iso_on_cover V L K e W hW
      (B.logParent ∘ Prod.fst) (C.logParent ∘ Prod.snd)
      (fun a => (hWL a).trans (B.logCover_subset a.1))
      (fun a => (hWK a).trans (C.logCover_subset a.2)) l k hl hk h h'
    · intro a x
      exact B.bundleLogCech_exp_point (Prod.fst ∘ a)
        ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le B.logCover W Prod.fst hWL a x.property⟩
    · intro a x
      exact C.bundleLogCech_exp_point (Prod.snd ∘ a)
        ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le C.logCover W Prod.snd hWK a x.property⟩
  exact ((Holomorphic.LogClassComparison.holomorphicLogUnitClass_refinement V.analyticModel V.analyticSpace
    B.logCover W Prod.fst hWL B.logCover_covers hW B.bundleLogCech
    (HolomorphicLineClass.nativeBundleLogCech_holomorphic V L) B.bundleLogCech_cocycle).symm.trans
      (hc.symm.trans (Holomorphic.LogClassComparison.holomorphicLogUnitClass_refinement V.analyticModel V.analyticSpace
        C.logCover W Prod.snd hWK C.logCover_covers hW C.bundleLogCech
        (HolomorphicLineClass.nativeBundleLogCech_holomorphic V K) C.bundleLogCech_cocycle)))

def nativeHolomorphicPicardClass : HilbertConstruction.Line.Bundles.LineBundle.IsoClass V.carrier →
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace :=
  Quotient.lift (HolomorphicLineClass.nativeHolomorphicLineClass V) (fun L K ⟨e⟩ => nativeHolomorphicLineClass_iso V L K e)

theorem nativeHolomorphicPicardClass_classOf :
    nativeHolomorphicPicardClass V (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = HolomorphicLineClass.nativeHolomorphicLineClass V L := rfl

theorem nativeHolomorphicPicardClass_chern (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass V.carrier) :
    DivisorClass.Chern.Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (nativeHolomorphicPicardClass V q) =
      ChernClasses.lineBundleClassChernClass V.presentation q := by
  induction q using Quotient.inductionOn with
  | h L => exact HolomorphicChernComparison.nativeHolomorphicLineClass_chern V L

end

/-! Zero native holomorphic class is equivalent to an actual
nowhere-vanishing holomorphic change of frame trivializing the original
algebraic transition units on their chosen logarithmic cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  {I : Type} (U : I → Opens M) (hU : ∀ x, ∃ i, x ∈ U i)
  (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1)
  (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1 k = 0)

local instance holomorphicTrivializationCohomologyGroup : AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of M) (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M) 1

theorem holomorphicUnitCech_trivialization_of_class_zero
    (hz : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) 0 k hk =
        (0 : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M)) :
    ∃ g : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U i))ˣ,
      ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
        (Holomorphic.LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x =
          (g (a 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
            (g (a 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩ := by
  let F := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M
  obtain ⟨b, hb⟩ := Cech.Add.cech_one_boundary_of_sheaf_class_zero (X := TopCat.of M) U F
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) k hk hz
  obtain ⟨s, hs⟩ := Cech.Add.cech_zero_eq_localSections (X := TopCat.of M) U F b
  let g (i : I) := Holomorphic.LogUnitClass.holomorphicUnitSection E M (U i) (s i)
  refine ⟨g, ?_⟩
  intro a x
  have hd := congrFun hb a
  rw [← hs, DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta] at hd
  have hv := congrArg (fun z => (Holomorphic.LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) z).val x) hd
  rw [Holomorphic.LogUnitClass.holomorphicUnitSection_value_sub] at hv
  exact hv.symm

theorem holomorphicUnitCech_class_zero_of_trivialization
    (g : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U i))ˣ)
    (hg : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      (Holomorphic.LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x =
        (g (a 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
          (g (a 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) 0 k hk =
        (0 : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M) := by
  let F := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M
  let b := DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections (X := TopCat.of M) U F (fun i => Additive.ofMul (g i))
  have hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U 0 b = k := by
    funext a
    apply Holomorphic.GlobalGluing.holomorphicUnitSection_ext E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
    intro x
    have hd := DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta (X := TopCat.of M) U F
      (fun i => Additive.ofMul (g i)) a
    have hv := congrArg (fun z => (Holomorphic.LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) z).val x) hd
    rw [Holomorphic.LogUnitClass.holomorphicUnitSection_value_sub] at hv
    exact hv.trans (hg a x).symm
  exact DivisorClass.Chern.Cech.SheafBoundaries.abelianCechSheafClass_eq_zero_of_boundary (X := TopCat.of M) U F
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) 0 k hk b hb

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier)

def NativeHolomorphicTrivialization : Prop :=
  ∃ g : ∀ i : (ChernClasses.nativeLineBundle V.presentation L).LogCoverIndex,
      (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := (ChernClasses.nativeLineBundle V.presentation L).logCover i))ˣ,
    ∀ (a : Fin 2 → (ChernClasses.nativeLineBundle V.presentation L).LogCoverIndex)
      (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ChernClasses.nativeLineBundle V.presentation L).logCover a),
      (ChernClasses.nativeLineBundle V.presentation L).pointTransition
        ((ChernClasses.nativeLineBundle V.presentation L).logParent (a 0))
        ((ChernClasses.nativeLineBundle V.presentation L).logParent (a 1)) x.val
        ((ChernClasses.nativeLineBundle V.presentation L).logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 x.property))
        ((ChernClasses.nativeLineBundle V.presentation L).logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 x.property)) =
          (g (a 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 x.property⟩ /
            (g (a 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 x.property⟩

theorem nativeHolomorphicLineClass_eq_zero_iff :
    HolomorphicLineClass.nativeHolomorphicLineClass V L = 0 ↔ NativeHolomorphicTrivialization V L := by
  let B := ChernClasses.nativeLineBundle V.presentation L
  let k := Holomorphic.LogUnitClass.holomorphicLogUnitCech V.analyticModel V.analyticSpace B.logCover B.bundleLogCech
    (HolomorphicLineClass.nativeBundleLogCech_holomorphic V L)
  have hk := Holomorphic.LogUnitClass.holomorphicLogUnitCech_closed V.analyticModel V.analyticSpace B.logCover B.bundleLogCech
    (HolomorphicLineClass.nativeBundleLogCech_holomorphic V L) B.bundleLogCech_cocycle
  constructor
  · intro hz
    obtain ⟨g, hg⟩ := holomorphicUnitCech_trivialization_of_class_zero V.analyticModel V.analyticSpace
      B.logCover B.logCover_covers k hk hz
    refine ⟨g, ?_⟩
    intro a x
    exact (HolomorphicLineClass.nativeHolomorphicLineClass_transition V L a x).symm.trans (hg a x)
  · rintro ⟨g, hg⟩
    apply holomorphicUnitCech_class_zero_of_trivialization V.analyticModel V.analyticSpace
      B.logCover B.logCover_covers k hk g
    intro a x
    exact (HolomorphicLineClass.nativeHolomorphicLineClass_transition V L a x).trans (hg a x)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass
