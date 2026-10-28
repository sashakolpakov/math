import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsClosed
import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.Localization

/-! # Generation Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GenerationLocalization.BundleCycles

noncomputable section

/-! Generation by actual projective Chow components glues across
an open base and its closed complement using genuine Chow localization. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X EU U EC C : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian EU] [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian EC] [AlgebraicGeometry.IsNoetherian C]
    [E.IsSeparated] [EU.IsSeparated] [EC.IsSeparated]
    (p : E ⟶ X) (qU : EU ⟶ U) (qC : EC ⟶ C)
    [Smooth p] [Smooth qU] [Smooth qC]
    [GeometricallyIntegral p] [GeometricallyIntegral qU] [GeometricallyIntegral qC]
    (i : U ⟶ X) (j : EU ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (k : C ⟶ X) (l : EC ⟶ E) [IsClosedImmersion k] [IsClosedImmersion l]
    (hsU : IsPullback qU j i p) (hsC : IsPullback qC l k p)
    (hc : Set.range k = (Set.range i)ᶜ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)
    (hU : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank qU r) (hC : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank qC r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (gU : ∀ d (α : DimensionChow.BundleCycles.DimensionChowQ (qU ≫ (i ≫ f)) d), α ∈ Filtration.BundleCycles.projectiveChowGenerated qU (i ≫ f) r hU (L.pullback j) d)
    (gC : ∀ d (α : DimensionChow.BundleCycles.DimensionChowQ (qC ≫ (k ≫ f)) d), α ∈ Filtration.BundleCycles.projectiveChowGenerated qC (k ≫ f) r hC (L.pullback l) d)

include hsU hsC hc gU gC in
theorem projectiveChowGeneration_of_open_closed (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :
    α ∈ Filtration.BundleCycles.projectiveChowGenerated p f r hp L d := by
  let h := AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p qU i j hsU f
  obtain ⟨γ, hγ, eγ⟩ := GeneratorsOpen.BundleCycles.projectiveChowGenerated_openRestriction_lift p qU i j hsU f r hp hU L d
    (DimensionChow.BundleCycles.dimensionChowTransport h d (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) d α)) (gU d _)
  have hz : Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) d (α - γ) = 0 := by
    apply DimensionChowTransportLaws.BundleCycles.dimensionChowTransport_injective h d
    rw [map_zero, map_sub, map_sub, eγ, sub_self]
  have hcomp : Set.range l = (Set.range j)ᶜ := by
    rw [AffineBundle.Localization.Cycles.schemePullback_range p qC k l hsC, AffineBundle.Localization.Cycles.schemePullback_range p qU i j hsU, hc, Set.preimage_compl]
  obtain ⟨β, hβ⟩ := (ChowLocalization.BundleCycles.openChowRestriction_eq_zero_iff j l hcomp (p ≫ f) d (α - γ)).mp hz
  have HB := GeneratorsClosed.BundleCycles.projectiveChowGenerated_closedPushforward p qC k l hsC f r hp hC L d
    (DimensionChow.BundleCycles.dimensionChowTransport (AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p qC k l hsC f) d β) (gC d _)
  rw [DimensionChowTransportLaws.BundleCycles.closedChowPushforwardOver_transport, hβ] at HB
  exact (sub_add_cancel α γ) ▸ Submodule.add_mem _ HB hγ

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GenerationLocalization.BundleCycles
