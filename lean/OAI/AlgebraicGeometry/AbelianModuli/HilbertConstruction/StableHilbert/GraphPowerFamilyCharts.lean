import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.LevelGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.OpenRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.CoverComparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.IsoPullbackTarget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RefinedChartRankCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.OpenCoverLocallyNoetherian

/-! # Graph Power Family Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerFamilyCharts.StableHilbertGraphPowerGluing

noncomputable section

/-! Original polarized families on a directed refinement of the actual
stable graph-power chart cover. Their comparisons are constructed from
the native stable-Hilbert family comparisons. In particular, the two
glued abelian schemes and their ordered level require no descent input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)
    (hd : 0 < d) (hδ : ∀ k, 0 < δ k)

abbrev familyCover : (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ).left.OpenCover :=
  Directed.OpenRefinement.directedOpenRefinement (GraphPowerGluing.StableHilbertGraphPowerGluing.glueData R i D H hH hD g Hm Hi N labels d δ Φ).openCover

instance familyCover_preorder :
    Preorder (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀ :=
  Directed.OpenRefinement.directedOpenRefinement_preorder (GraphPowerGluing.StableHilbertGraphPowerGluing.glueData R i D H hH hD g Hm Hi N labels d δ Φ).openCover

instance familyCover_locallyDirected :
    (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).LocallyDirected :=
  Directed.OpenRefinement.directedOpenRefinement_locallyDirected (GraphPowerGluing.StableHilbertGraphPowerGluing.glueData R i D H hH hD g Hm Hi N labels d δ Φ).openCover

abbrev refinedTest (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) : Over (Spec (.of R)) :=
  Embedded.FamilyOpenCover.overOpenCoverObject (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ) (familyCover R i D H hH hD g Hm Hi N
  labels d δ Φ) v

instance refinedTest_locallyNoetherian
    (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    IsLocallyNoetherian (refinedTest R i D H hH hD g Hm Hi N labels d δ Φ v).left :=
  HilbertConstruction.Over.OpenCoverLocallyNoetherian.overOpenCoverObject_locallyNoetherian
    (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ)
    (familyCover R i D H hH hD g Hm Hi N labels d δ Φ) v

def refinedChartMap (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    refinedTest R i D H hH hD g Hm Hi N labels d δ Φ v ⟶ (GraphPowerParameter.StableHilbertGraphPower.parameter R i v.1 D H hH g Hm
      Hi N labels d δ Φ) := by
  let C₀ : (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ).left.OpenCover :=
    (GraphPowerGluing.StableHilbertGraphPowerGluing.glueData R i D H hH hD g Hm Hi N labels d δ Φ).openCover
  let f := Directed.OpenRefinement.directedOpenRefinement_toMember C₀ v
  have hc : C₀.f v.1 ≫ (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ).hom =
    (GraphPowerParameter.StableHilbertGraphPower.parameter R i v.1 D H hH g Hm Hi N labels d δ Φ).hom := (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g
    Hm Hi N labels d δ Φ v.1).w
  exact Over.homMk f ((congrArg (fun q => f ≫ q) hc.symm).trans
    ((Category.assoc f (C₀.f v.1) (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ).hom).symm.trans
      (congrArg (fun q => q ≫ (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ).hom)
        (Directed.OpenRefinement.directedOpenRefinement_toMember_map C₀ v))))

theorem refinedChartMap_toBase (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    (refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ v) ≫ (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ v.1) = Embedded.FamilyOpenCover.overOpenCoverMap (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ) (familyCover R i D H hH hD g Hm
      Hi N labels d δ Φ) v := by
  apply Over.OverMorphism.ext
  exact Directed.OpenRefinement.directedOpenRefinement_toMember_map
    (GraphPowerGluing.StableHilbertGraphPowerGluing.glueData R i D H hH hD g Hm Hi N labels d δ Φ).openCover v

def refinedChartMap_rank (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :=
  PLift.up (RefinedChartRankCompatibility.compositeRankMap_from_namedChart (C := Over (Spec (.of R)))
    (refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ v)
    (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ v.1)
    (Embedded.FamilyOpenCover.overOpenCoverMap (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ)
      (familyCover R i D H hH hD g Hm Hi N labels d δ Φ) v)
    (GraphPowerGluing.StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ)
    (GraphPowerParameter.StableHilbertGraphPower.inclusion R i v.1 D H hH g Hm Hi N labels d δ Φ)
    (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i v.1 D H hH g Hm Hi N labels)
    (Scheme.stableHilbertChartOver R i D H hH hD v.1)
    (Scheme.stableHilbertRankParameterOver R i D H hH hD)
    (ChartPullbacks.stableHilbertChartToRank R i v.1 D H)
    (GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i v.1 D H hH g Hm Hi N labels d δ Φ)
    rfl
    (refinedChartMap_toBase R i D H hH hD g Hm Hi N labels d δ Φ v)
    (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap_inclusion R i D H hH hD g Hm Hi N labels d δ Φ v.1)
    (Scheme.stableHilbertChartOver_rankParameter R i D H hH hD v.1))

abbrev refinedBaseMap {v w : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀} (f : v ⟶ w) :=
  Embedded.CoverComparisons.overOpenCoverTransition (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ) (familyCover R i D H hH hD g Hm Hi N
  labels d δ Φ) f

theorem refinedBaseMap_left
    {v w : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀} (f : v ⟶ w) :
    (refinedBaseMap R i D H hH hD g Hm Hi N labels d δ Φ f).left =
      (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).trans f := rfl

def refined_rank_after_baseMap
    {v w : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀} (f : v ⟶ w) :=
  PLift.up (RefinedChartRankCompatibility.compositeRankMap_after_coverTransition (C := Over (Spec (.of R)))
    (refinedChartMap_rank R i D H hH hD g Hm Hi N labels d δ Φ w).down
    (Embedded.CoverComparisons.overOpenCoverTransition_map (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ)
      (familyCover R i D H hH hD g Hm Hi N labels d δ Φ) f))

def refined_rank_compatible
    {v w : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀} (f : v ⟶ w) :=
  PLift.up (RefinedChartRankCompatibility.rankMaps_eq_of_same_target
    (refinedChartMap_rank R i D H hH hD g Hm Hi N labels d δ Φ v).down
    (refined_rank_after_baseMap R i D H hH hD g Hm Hi N labels d δ Φ f).down)

def refinedFamily (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) : PolarizationData.PolarizedAbelianWithFullLevel g δ
  N ((familyCover R i D H hH hD g Hm Hi N labels d δ Φ).X v) :=
  (GraphPowerParameter.StableHilbertGraphPower.universalFamily R i v.1 D H hH g Hm Hi N labels d δ Φ).pullback (refinedChartMap R i
    D H hH hD g Hm Hi N labels d δ Φ v).left

/-- The comparison on the original directed overlap is obtained from
the original stable-Hilbert comparison, including dual, polarization,
Poincare class, and every ordered level label. -/
def refinedFamilyIso {v w : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀} (f : v ⟶ w) :
    Moduli.Isomorphisms.LevelPreservingIso
      (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ v)
      ((refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ w).pullback
        ((familyCover R i D H hH hD g Hm Hi N labels d δ Φ).trans f)) := by
  let e := GraphPowerPointComparison.StableHilbertGraphPowerPointComparison.iso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ
    v.1 w.1 (refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ v)
    (refinedBaseMap R i D H hH hD g Hm Hi N labels d δ Φ f ≫
      refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ w)
    (refined_rank_compatible R i D H hH hD g Hm Hi N labels d δ Φ f).down
  exact Moduli.Isomorphisms.LevelPreservingIso.transPullbackCompOfEq
    (GraphPowerParameter.StableHilbertGraphPower.universalFamily R i w.1 D H hH g Hm Hi N labels d δ Φ)
    (refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ w).left
    ((familyCover R i D H hH hD g Hm Hi N labels d δ Φ).trans f)
    (refinedBaseMap R i D H hH hD g Hm Hi N labels d δ Φ f ≫
      refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ w).left
    (congrArg (fun t => t ≫ (refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ w).left)
      (refinedBaseMap_left R i D H hH hD g Hm Hi N labels d δ Φ f)) e

variable (hN : 3 ≤ N)

def abelian : Abelian.Schemes.AbelianScheme g (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ).left :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian (familyCover R i D H hH hD g Hm Hi N labels d δ Φ)
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ)

def dualAbelian : Abelian.Schemes.AbelianScheme g (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ).left :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualAbelian (familyCover R i D H hH hD g Hm Hi N labels d δ Φ)
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ)

def level : (StableHilbertGraphPowerGluing.abelian R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).FullLevel N :=
  Directed.LevelGluing.DirectedPolarizedSchemeGluing.level (familyCover R i D H hH hD g Hm Hi N labels d δ Φ)
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ)

def abelianRefinedIso (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ v).abelian.scheme ≅
      ((StableHilbertGraphPowerGluing.abelian R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).pullback ((familyCover R i D H hH hD g Hm Hi N labels d δ Φ).f v)).scheme :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso (familyCover R i D H hH hD g Hm Hi N labels d δ Φ)
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ) v

instance abelianRefinedIso_group (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    IsMonHom (abelianRefinedIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN v).hom :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso_group (familyCover R i D H hH hD g Hm Hi N labels d δ Φ)
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ) v

def dualRefinedIso (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ v).dual.abelian.scheme ≅
      ((dualAbelian R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).pullback ((familyCover R i D H hH hD g Hm Hi N
        labels d δ Φ).f v)).scheme :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso (familyCover R i D H hH hD g Hm Hi N labels d δ Φ)
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ) v

instance dualRefinedIso_group (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    IsMonHom (dualRefinedIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN v).hom :=
  Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso_group (familyCover R i D H hH hD g Hm Hi N labels d δ Φ)
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ) v

theorem abelianRefinedIso_level (v : (familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ v).level.transport
      (abelianRefinedIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN v) =
      (StableHilbertGraphPowerGluing.level R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).pullback ((familyCover R i D H hH hD g Hm Hi N labels d δ Φ).f v) :=
  Directed.LevelGluing.DirectedPolarizedSchemeGluing.chartIso_level (familyCover R i D H hH hD g Hm Hi N labels d δ Φ)
    (refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN
    (refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ) v

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerFamilyCharts.StableHilbertGraphPowerGluing
