import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogClassComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousChernVanishing
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogTransition

/-! # Holomorphic Chern Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicChernComparison

noncomputable section

/-! The native holomorphic unit class of an actual algebraic line bundle
has exactly the original native Chern class. Common refinement and an
actual change of trivialization prove the comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogTransition
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [NormalSpace M]

theorem holomorphicLogUnitClass_original (u : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    Holomorphic.LogUnitClass.holomorphicLogUnitClass E M (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCover E M u) (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCech E M u)
      (DivisorClass.Chern.Holomorphic.ChernSheaf.holomorphicLogCech_holomorphic E M u) (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCech_cocycle E M u)
      (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCover_covers E M u) = u := by
  have he : Holomorphic.LogUnitClass.holomorphicLogUnitCech E M (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCover E M u) (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCech E M u)
      (DivisorClass.Chern.Holomorphic.ChernSheaf.holomorphicLogCech_holomorphic E M u) = DivisorClass.Chern.Holomorphic.LogTransition.holomorphicLogTransitionCech E M u :=
    DivisorClass.Chern.Holomorphic.LogTransition.holomorphicLogTransitionCech_exponential E M u
  exact (Cech.Add.cechSheafClass_congr (X := TopCat.of M) (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCover E M u)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCover E M u)
      (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCover_covers E M u)) 0 _ _
    (Holomorphic.LogUnitClass.holomorphicLogUnitCech_closed E M _ _ (DivisorClass.Chern.Holomorphic.ChernSheaf.holomorphicLogCech_holomorphic E M u)
      (DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCech_cocycle E M u))
    (DivisorClass.Chern.Holomorphic.LogTransition.holomorphicLogTransitionCech_closed E M u) he).trans
      (DivisorClass.Chern.Holomorphic.LogTransition.holomorphicLogTransitionCech_sheaf_class E M u)

theorem holomorphicFirstChernClassQ_logUnitClass {I : Type} (U : I → Opens M)
    (hU : ∀ x, ∃ i, x ∈ U i) (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of M) U)
    (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a))
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l) :
    DivisorClass.Chern.Holomorphic.Singular.holomorphicFirstChernClassQ E M (Holomorphic.LogUnitClass.holomorphicLogUnitClass E M U l hl h hU) =
      DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of M) U hU l h := by
  let u := Holomorphic.LogUnitClass.holomorphicLogUnitClass E M U l hl h hU
  let V := DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCover E M u
  let m := DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCech E M u
  have hV := DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCover_covers E M u
  have hm := DivisorClass.Chern.Holomorphic.Singular.holomorphicLogCech_cocycle E M u
  have hml := DivisorClass.Chern.Holomorphic.ChernSheaf.holomorphicLogCech_holomorphic E M u
  let W : I × DivisorClass.Chern.Holomorphic.Singular.HolomorphicLogIndex E M u → Opens M := fun a => U a.1 ⊓ V a.2
  have hW : ∀ x, ∃ a, x ∈ W a := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨j, hj⟩ := hV x
    exact ⟨(i, j), hi, hj⟩
  have hWU : ∀ a, W a ≤ U a.1 := fun _ => inf_le_left
  have hWV : ∀ a, W a ≤ V a.2 := fun _ => inf_le_right
  let k := DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech (TopCat.of M) U W Prod.fst hWU l
  let k' := DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech (TopCat.of M) V W Prod.snd hWV m
  have hk := DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement (TopCat.of M) U W Prod.fst hWU l h
  have hk' := DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement (TopCat.of M) V W Prod.snd hWV m hm
  have hkl := Holomorphic.LogClassComparison.holomorphic_refineLogCech E M U W Prod.fst hWU l hl
  have hkl' := Holomorphic.LogClassComparison.holomorphic_refineLogCech E M V W Prod.snd hWV m hml
  have he : Holomorphic.LogUnitClass.holomorphicLogUnitClass E M W k' hkl' hk' hW =
      Holomorphic.LogUnitClass.holomorphicLogUnitClass E M W k hkl hk hW :=
    (Holomorphic.LogClassComparison.holomorphicLogUnitClass_refinement E M V W Prod.snd hWV hV hW m hml hm).trans
      ((holomorphicLogUnitClass_original E M u).trans
        (Holomorphic.LogClassComparison.holomorphicLogUnitClass_refinement E M U W Prod.fst hWU hU hW l hl h).symm)
  have hc := Holomorphic.LogClassComparison.logarithmicChern_eq_of_holomorphicClass_eq E M W hW k k' hkl hkl' hk hk' he
  exact (DivisorClass.Chern.LogRefinement.RationalCech.logarithmicSingularClass_refinement (TopCat.of M) V W Prod.snd hWV hV hW m hm).symm.trans
    (hc.trans (DivisorClass.Chern.LogRefinement.RationalCech.logarithmicSingularClass_refinement (TopCat.of M) U W Prod.fst hWU hU hW l h))

theorem nativeHolomorphicLineClass_chern (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier) :
    DivisorClass.Chern.Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (HolomorphicLineClass.nativeHolomorphicLineClass V L) =
      ChernClasses.lineBundleChernClass V.presentation L :=
  holomorphicFirstChernClassQ_logUnitClass V.analyticModel V.analyticSpace
    (ChernClasses.nativeLineBundle V.presentation L).logCover (ChernClasses.nativeLineBundle V.presentation L).logCover_covers
    (ChernClasses.nativeLineBundle V.presentation L).bundleLogCech (HolomorphicLineClass.nativeBundleLogCech_holomorphic V L)
    (ChernClasses.nativeLineBundle V.presentation L).bundleLogCech_cocycle

theorem homogeneousLineBundle_holomorphicChern_eq_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    DivisorClass.Chern.Holomorphic.Singular.holomorphicFirstChernClassQ A.variety.analyticModel A.variety.analyticSpace
      (HolomorphicLineClass.nativeHolomorphicLineClass A.variety L) = 0 :=
  (nativeHolomorphicLineClass_chern A.variety L).trans (HomogeneousChernVanishing.homogeneousLineBundle_chern_eq_zero A L hL)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicChernComparison
