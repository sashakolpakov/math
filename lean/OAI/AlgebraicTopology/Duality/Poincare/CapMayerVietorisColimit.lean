import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportMayerVietoris
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpen
import OAI.AlgebraicTopology.Duality.Poincare.OpenRational
import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap

/-! # Cap Mayer Vietoris Colimit -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisColimit

noncomputable section

/-!
# Compact-pair detection of the canonical cap connecting square

The genuine compact-pair stages jointly detect maps out of compactly supported
cohomology of an open union. This file reduces the canonical cap connecting
square to explicit relative-cap identities at those stages. The stage
identities remain explicit hypotheses here and must be proved separately.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section CompactPairDetection

variable {X : TopCat.{0}} [T2Space X]

/-- The actual compact-pair colimit is the native compact-support cohomology
of the open union, by the proved compact decomposition and open excision. -/
def compactSupportPairOpenUnionColimitIso (U V : Opens X) (n : ℕ) :
    colimit (CompactSupportPairIndex.compactSupportPairUnionDiagram (ModuleCat.of ℚ ℚ) U V n) ≅
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ↥(U ⊔ V)) n :=
  CompactSupportPairIndex.compactSupportPairUnionColimitIso (ModuleCat.of ℚ ℚ) U V n ≪≫
    CompactSupportOpen.compactSupportOpenIndexIso (U ⊔ V) n

@[reassoc (attr := simp)]
theorem compactSupportPairOpenUnionColimitIso_ι (U V : Opens X) (n : ℕ)
    (K : U.compactsInside × V.compactsInside) :
    colimit.ι (CompactSupportPairIndex.compactSupportPairUnionDiagram (ModuleCat.of ℚ ℚ) U V n) K ≫
        (compactSupportPairOpenUnionColimitIso U V n).hom =
      CompactSupportOpen.compactSupportOpenStageClass (U ⊔ V) (CompactSupportDecomposition.compactPairUnion U V K) n := by
  change colimit.ι _ K ≫
    (CompactSupportPairIndex.compactSupportPairUnionColimitIso (ModuleCat.of ℚ ℚ) U V n).hom ≫
      (CompactSupportOpen.compactSupportOpenIndexIso (U ⊔ V) n).hom = _
  rw [CompactSupportPairIndex.compactSupportPairUnionColimitIso_ι_assoc]
  rfl

/-- Equality on all genuine compact-pair stages implies equality of maps
out of the native compact-support cohomology of the open union. -/
theorem compactSupportPairOpenStage_hom_ext (U V : Opens X) (n : ℕ)
    {T : ModuleCat.{0} ℚ}
    {f g : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ↥(U ⊔ V)) n ⟶ T}
    (h : ∀ K : U.compactsInside × V.compactsInside,
      CompactSupportOpen.compactSupportOpenStageClass (U ⊔ V) (CompactSupportDecomposition.compactPairUnion U V K) n ≫ f =
        CompactSupportOpen.compactSupportOpenStageClass (U ⊔ V) (CompactSupportDecomposition.compactPairUnion U V K) n ≫ g) : f = g := by
  apply (cancel_epi (compactSupportPairOpenUnionColimitIso U V n).hom).mp
  apply colimit.hom_ext
  intro K
  simpa only [compactSupportPairOpenUnionColimitIso_ι_assoc] using h K

end CompactPairDetection

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- Restrict an ambient supported class to its actual support preimage in
the open submanifold, then cap with its actual canonical fundamental class. -/
def complexManifoldOpenStageCap (U : Opens M) (K : U.compactsInside)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) (X := TopCat.of M) U p).obj K ⟶
      OpenRational.openRationalHomology (X := TopCat.of M) U q :=
  CompactSupportOpen.compactSupportOpenPreimageCohomologyRestriction (X := TopCat.of M) U K p ≫
    SupportCapNaturality.relativeCapWithClass (TopCat.of U) (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ p q
      (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq (CompactOpenIndex.openCompactPreimage U K))

/-- The actual compact-stage computation of the canonical cap map in an
open submanifold, including its relative restriction map. -/
@[reassoc]
theorem complexManifoldCompactSupportCap_openStage (U : Opens M) (K : U.compactsInside)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportOpen.compactSupportOpenStageClass (X := TopCat.of M) U K p ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq =
      complexManifoldOpenStageCap d U K p q hpq := by
  rw [CompactSupportOpen.compactSupportOpenStageClass_preimage, Category.assoc,
    ComplexManifoldCap.complexManifoldCompactSupportCap_stage]
  rfl

/-- The native canonical cap connecting square follows from the precise
relative-cap identity at every actual compact pair. This theorem transports
that identity and does not assume it silently. -/
theorem complexManifoldCap_mayerVietoris_of_stages (U V : Opens M)
    (p q : ℕ) (hpq : p + (q + 1) = 2 * d)
    (hstage : ∀ K : U.compactsInside × V.compactsInside,
      complexManifoldOpenStageCap d (M := M) (U ⊔ V)
          (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K) p (q + 1) hpq ≫
          OpenRational.openRationalMayerVietorisBoundary (X := TopCat.of M) U V q =
        ((-1 : ℤ) ^ (p + 1)) •
          ((CompactSupportMayerVietoris.compactSupportPairBoundary (X := TopCat.of M) U V p).app K ≫
            complexManifoldOpenStageCap d (M := M) (U ⊓ V)
              (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K)
              (p + 1) q (by omega))) :
    ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊔ V)) p (q + 1) hpq ≫
        OpenRational.openRationalMayerVietorisBoundary (X := TopCat.of M) U V q =
      ((-1 : ℤ) ^ (p + 1)) •
        (CompactSupportMayerVietoris.compactSupportMayerVietorisBoundary (X := TopCat.of M) U V p ≫
          ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) (p + 1) q (by omega)) := by
  apply compactSupportPairOpenStage_hom_ext (X := TopCat.of M) U V p
  intro K
  rw [Preadditive.comp_zsmul,
    CompactSupportMayerVietoris.compactSupportMayerVietorisBoundary_stage_assoc,
    complexManifoldCompactSupportCap_openStage_assoc,
    complexManifoldCompactSupportCap_openStage]
  exact hstage K

end

end OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisColimit
