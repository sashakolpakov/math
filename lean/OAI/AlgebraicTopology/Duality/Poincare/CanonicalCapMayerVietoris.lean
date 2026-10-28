import OAI.AlgebraicTopology.Duality.Poincare.SupportedCapMayerVietoris
import OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalSupportCapEndpoints
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalSmallSupportRepresentative

/-! # Canonical Cap Mayer Vietoris -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapMayerVietoris

noncomputable section

/-!
# The canonical cap-product Mayer--Vietoris connecting square

The actual canonical integral fundamental class is represented by one
simultaneously small relative chain. Actual support-connecting cochains cap
that chain to local chains whose signed boundaries agree on the intersection.
The resulting identity descends through the genuine compact-pair colimit.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The canonical connecting identity on an actual compactly supported
cocycle, proved using genuine cochain lifts and one canonical small chain. -/
theorem complexManifoldCap_mayerVietoris_stage_cocycle
    (U V : Opens M) (K : U.compactsInside × V.compactsInside)
    (p q : ℕ) (hpq : p + (q + 1) = 2 * d)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of M) ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) p) :
    OpenRational.openRationalMayerVietorisBoundary (X := TopCat.of M) U V q
        (CapMayerVietorisColimit.complexManifoldOpenStageCap d (M := M) (U ⊔ V) (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K) p (q + 1) hpq
          (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)
            ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) p a)) =
      ((-1 : ℤ) ^ (p + 1)) •
        CapMayerVietorisColimit.complexManifoldOpenStageCap d (M := M) (U ⊓ V) (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K)
          (p + 1) q (by omega)
          (SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary (TopCat.of M) K.1.val K.2.val
            K.1.val.isCompact.isClosed K.2.val.isCompact.isClosed p (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)
            ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) p a)) := by
  let X : TopCat.{0} := TopCat.of M
  let K₁ : Set M := K.1.val
  let K₂ : Set M := K.2.val
  let KI := CompactSupportPairIndex.compactPairIntersection (X := X) U V K
  obtain ⟨bK, bL, c, hab, hdK, hdL, hδ⟩ :=
    SupportConnectingAmbient.supportConnecting_components_support_ambient X K₁ K₂
      K.1.val.isCompact.isClosed K.2.val.isCompact.isClosed p a
  obtain ⟨s, hs, hUnion, hi, hIntersection⟩ :=
    CanonicalSmallSupportRepresentative.exists_canonicalSmallSupportRepresentative d (M := M) U V K p q hpq
  let t := CapMayerVietorisChains.smallSupportChainCast X U V K₁ K₂
    (by omega : p + q + 1 = (p + 1) + q) s
  have hucap := CanonicalSupportCapEndpoints.smallSupportUnionCapCycle_class_eq_stage d (M := M)
    U V K p (q + 1) hpq a s hs hUnion
  have hicap := CanonicalSupportCapEndpoints.smallSupportIntersectionCapCycle_class_eq_stage d (M := M)
    U V K (p + 1) q (by omega) c t hi hIntersection
  have hraw := SupportedCapMayerVietoris.supportedCapMayerVietoris_chain_identity (X := X)
    U V K₁ K₂ p q a bK bL c s hs hi hab hdK hdL
  have hend := congrArg (fun z => ((-1 : ℤ) ^ (p + 1)) •
    CapMayerVietorisColimit.complexManifoldOpenStageCap d (M := M) (U ⊓ V) KI (p + 1) q (by omega) z) hδ.symm
  exact (congrArg (OpenRational.openRationalMayerVietorisBoundary (X := X) U V q) hucap.symm).trans
    (hraw.trans ((congrArg (fun z => ((-1 : ℤ) ^ (p + 1)) • z) hicap).trans hend))

/-- The actual canonical cap connecting square at every genuine compact-pair stage. -/
theorem complexManifoldCap_mayerVietoris_stage
    (U V : Opens M) (K : U.compactsInside × V.compactsInside)
    (p q : ℕ) (hpq : p + (q + 1) = 2 * d) :
    CapMayerVietorisColimit.complexManifoldOpenStageCap d (M := M) (U ⊔ V) (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K) p (q + 1) hpq ≫
        OpenRational.openRationalMayerVietorisBoundary (X := TopCat.of M) U V q =
      ((-1 : ℤ) ^ (p + 1)) •
        ((CompactSupportMayerVietoris.compactSupportPairBoundary (X := TopCat.of M) U V p).app K ≫
          CapMayerVietorisColimit.complexManifoldOpenStageCap d (M := M) (U ⊓ V) (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K)
            (p + 1) q (by omega)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)
      ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) p x
  exact complexManifoldCap_mayerVietoris_stage_cocycle d (M := M) U V K p q hpq a

/-- The canonical cap map intertwines the genuine compact-support and
ordinary open-set connecting homomorphisms with the cap-boundary sign. -/
theorem complexManifoldCap_mayerVietoris (U V : Opens M)
    (p q : ℕ) (hpq : p + (q + 1) = 2 * d) :
    ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊔ V)) p (q + 1) hpq ≫
        OpenRational.openRationalMayerVietorisBoundary (X := TopCat.of M) U V q =
      ((-1 : ℤ) ^ (p + 1)) •
        (CompactSupportMayerVietoris.compactSupportMayerVietorisBoundary (X := TopCat.of M) U V p ≫
          ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) (p + 1) q (by omega)) :=
  CapMayerVietorisColimit.complexManifoldCap_mayerVietoris_of_stages d (M := M) U V p q hpq
    (fun K => complexManifoldCap_mayerVietoris_stage d (M := M) U V K p q hpq)

end

end OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapMayerVietoris
