import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.LevelGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.OpenRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.CoverComparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.IsoPullbackTarget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RefinedChartRankCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.OpenCoverLocallyNoetherian

/-! # Polarization Family Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationFamilyCharts.StableHilbertPolarizationGluing

noncomputable section

/-! Original polarized families on a directed refinement of the actual
stable polarization chart cover. Their comparisons are constructed from
the native stable-Hilbert family comparisons. In particular, the two
glued abelian schemes and their ordered level require no descent input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

abbrev familyCover : (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left.OpenCover :=
  Directed.OpenRefinement.directedOpenRefinement (PolarizationGluing.StableHilbertPolarizationGluing.glueData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).openCover

instance familyCover_preorder :
    Preorder (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀ :=
  Directed.OpenRefinement.directedOpenRefinement_preorder (PolarizationGluing.StableHilbertPolarizationGluing.glueData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).openCover

instance familyCover_locallyDirected :
    (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).LocallyDirected :=
  Directed.OpenRefinement.directedOpenRefinement_locallyDirected (PolarizationGluing.StableHilbertPolarizationGluing.glueData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).openCover

abbrev refinedTest (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) : Over (Spec (.of R)) :=
  Embedded.FamilyOpenCover.overOpenCoverObject (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (familyCover R i D H hH hD g Hm Hi N
  labels qR d hd δ hδ) v

instance refinedTest_locallyNoetherian
    (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    IsLocallyNoetherian (refinedTest R i D H hH hD g Hm Hi N labels qR d hd δ hδ v).left :=
  HilbertConstruction.Over.OpenCoverLocallyNoetherian.overOpenCoverObject_locallyNoetherian
    (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v

def refinedChartMap (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    refinedTest R i D H hH hD g Hm Hi N labels qR d hd δ hδ v ⟶ (PolarizationParameter.StableHilbertPolarization.parameter R i v.1 D H hH g Hm
      Hi N labels qR d hd δ hδ) := by
  let C₀ : (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left.OpenCover :=
    (PolarizationGluing.StableHilbertPolarizationGluing.glueData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).openCover
  let f := Directed.OpenRefinement.directedOpenRefinement_toMember C₀ v
  have hc : C₀.f v.1 ≫ (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).hom =
    (PolarizationParameter.StableHilbertPolarization.parameter R i v.1 D H hH g Hm Hi N labels qR d hd δ hδ).hom := (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g
    Hm Hi N labels qR d hd δ hδ v.1).w
  exact Over.homMk f ((congrArg (fun q => f ≫ q) hc.symm).trans
    ((Category.assoc f (C₀.f v.1) (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).hom).symm.trans
      (congrArg (fun q => q ≫ (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).hom)
        (Directed.OpenRefinement.directedOpenRefinement_toMember_map C₀ v))))

theorem refinedChartMap_toBase (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    (refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ v) ≫ (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ
      hδ v.1) = Embedded.FamilyOpenCover.overOpenCoverMap (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (familyCover R i D H hH hD g Hm
      Hi N labels qR d hd δ hδ) v := by
  apply Over.OverMorphism.ext
  exact Directed.OpenRefinement.directedOpenRefinement_toMember_map
    (PolarizationGluing.StableHilbertPolarizationGluing.glueData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).openCover v

theorem refinedChartMap_rank (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    (((refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ v) ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i v.1 D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i v.1 D H hH g Hm Hi N labels)) ≫ (ChartPullbacks.stableHilbertChartToRank R i v.1 D H) =
      ((Embedded.FamilyOpenCover.overOpenCoverMap (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v) ≫ (PolarizationGluing.StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ)) ≫ (Scheme.stableHilbertRankParameterOver R i D H hH hD) := by
  convert (RefinedChartRankCompatibility.compositeRankMap_from_namedChart (C := Over (Spec (.of R)))
    (refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ v)
    (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ v.1)
    (Embedded.FamilyOpenCover.overOpenCoverMap (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
      (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v)
    (PolarizationGluing.StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (PolarizationParameter.StableHilbertPolarization.inclusion R i v.1 D H hH g Hm Hi N labels qR d hd δ hδ)
    (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i v.1 D H hH g Hm Hi N labels)
    (Scheme.stableHilbertChartOver R i D H hH hD v.1)
    (Scheme.stableHilbertRankParameterOver R i D H hH hD)
    (ChartPullbacks.stableHilbertChartToRank R i v.1 D H)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i v.1 D H hH g Hm Hi N labels qR d hd δ hδ)
    rfl
    (refinedChartMap_toBase R i D H hH hD g Hm Hi N labels qR d hd δ hδ v)
    (PolarizationGluing.StableHilbertPolarizationGluing.chartMap_inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ v.1)
    (Scheme.stableHilbertChartOver_rankParameter R i D H hH hD v.1)) using 2

abbrev refinedBaseMap {v w : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀} (f : v ⟶ w) :=
  Embedded.CoverComparisons.overOpenCoverTransition (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (familyCover R i D H hH hD g Hm Hi N
  labels qR d hd δ hδ) f

theorem refinedBaseMap_left
    {v w : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀} (f : v ⟶ w) :
    (refinedBaseMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ f).left =
      (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).trans f := rfl

theorem refined_rank_after_baseMap
    {v w : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀} (f : v ⟶ w) :
    ((((Embedded.CoverComparisons.overOpenCoverTransition (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) f) ≫ (refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ w)) ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i w.1 D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i w.1 D H hH g Hm Hi N labels)) ≫ (ChartPullbacks.stableHilbertChartToRank R i w.1 D H) =
      ((Embedded.FamilyOpenCover.overOpenCoverMap (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v) ≫ (PolarizationGluing.StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ)) ≫ (Scheme.stableHilbertRankParameterOver R i D H hH hD) :=
  RefinedChartRankCompatibility.compositeRankMap_after_coverTransition (C := Over (Spec (.of R)))
    (refinedChartMap_rank R i D H hH hD g Hm Hi N labels qR d hd δ hδ w)
    (Embedded.CoverComparisons.overOpenCoverTransition_map (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
      (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) f)

theorem refined_rank_compatible
    {v w : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀} (f : v ⟶ w) :
    (((refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ v) ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i v.1 D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i v.1 D H hH g Hm Hi N labels)) ≫ (ChartPullbacks.stableHilbertChartToRank R i v.1 D H) =
      ((((Embedded.CoverComparisons.overOpenCoverTransition (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) f) ≫ (refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ w)) ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i w.1 D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i w.1 D H hH g Hm Hi N labels)) ≫ (ChartPullbacks.stableHilbertChartToRank R i w.1 D H) :=
  RefinedChartRankCompatibility.rankMaps_eq_of_same_target
    (refinedChartMap_rank R i D H hH hD g Hm Hi N labels qR d hd δ hδ v)
    (refined_rank_after_baseMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ f)

def refinedFamily (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) : PolarizationData.PolarizedAbelianWithFullLevel g δ
  N ((familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).X v) :=
  (PolarizationParameter.StableHilbertPolarization.universalFamily R i v.1 D H hH g Hm Hi N labels qR d hd δ hδ).pullback (refinedChartMap R i
    D H hH hD g Hm Hi N labels qR d hd δ hδ v).left

/-- The comparison on the original directed overlap is obtained from
the original stable-Hilbert comparison, including dual, polarization,
Poincare class, and every ordered level label. -/
def refinedFamilyIso {v w : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀} (f : v ⟶ w) :
    Moduli.Isomorphisms.LevelPreservingIso
      (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ v)
      ((refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ w).pullback
        ((familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).trans f)) := by
  let e := PolarizationPointComparison.StableHilbertPolarizationPointComparison.iso R i D H hH hD g Hm Hi N labels qR d hd δ hδ
    v.1 w.1 (refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ v)
    (refinedBaseMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ f ≫
      refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ w)
    (refined_rank_compatible R i D H hH hD g Hm Hi N labels qR d hd δ hδ f)
  exact Moduli.Isomorphisms.LevelPreservingIso.transPullbackCompOfEq
    (PolarizationParameter.StableHilbertPolarization.universalFamily R i w.1 D H hH g Hm Hi N labels qR d hd δ hδ)
    (refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ w).left
    ((familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).trans f)
    (refinedBaseMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ f ≫
      refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ w).left
    (congrArg (fun t => t ≫ (refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ w).left)
      (refinedBaseMap_left R i D H hH hD g Hm Hi N labels qR d hd δ hδ f)) e

variable (hN : 3 ≤ N)

def abelian : Abelian.Schemes.AbelianScheme g (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ)

def dualAbelian : Abelian.Schemes.AbelianScheme g (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualAbelian (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ)

def level : (StableHilbertPolarizationGluing.abelian R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).FullLevel N :=
  Directed.LevelGluing.DirectedPolarizedSchemeGluing.level (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ)

def abelianRefinedIso (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ v).abelian.scheme ≅
      ((StableHilbertPolarizationGluing.abelian R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).pullback ((familyCover R i D H hH hD g Hm Hi N labels qR
        d hd δ hδ).f v)).scheme :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v

instance abelianRefinedIso_group (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    IsMonHom (abelianRefinedIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN v).hom :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso_group (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v

def dualRefinedIso (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ v).dual.abelian.scheme ≅
      ((dualAbelian R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).pullback ((familyCover R i D H hH hD g Hm Hi N
        labels qR d hd δ hδ).f v)).scheme :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v

instance dualRefinedIso_group (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    IsMonHom (dualRefinedIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN v).hom :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso_group (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v

theorem abelianRefinedIso_level (v : (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ v).level.transport
      (abelianRefinedIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN v) =
      (StableHilbertPolarizationGluing.level R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).pullback ((familyCover R i D H hH hD g Hm Hi N labels qR d
        hd δ hδ).f v) :=
  Directed.LevelGluing.DirectedPolarizedSchemeGluing.chartIso_level (familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
    (refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationFamilyCharts.StableHilbertPolarizationGluing
