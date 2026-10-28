import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationMarkedPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroGraphPowerSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.MarkedOrbits

/-! # Polarization Coordinate Orbits -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationCoordinateOrbits.StableHilbertPolarization

noncomputable section

/-! An original polarized full-level isomorphism between points of
uniform stable charts identifies their points of the original balanced
quotient. Completeness is derived from the uniform graph rank and the
specified marked frame, and the zero mark removes the base line twist. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem markedSectionData_eq
    {S : Scheme.{0}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) {L : Line.Bundles.LineBundle A.scheme.left}
    (E : P.SectionData L) (c : Multiplicative (Fin (2 * g) → ZMod N))
    (q : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S P.dimension)
    (h : Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A level P c = q) :
    Over.homMk (A.fullLevelGlobalSection level c) (A.fullLevelGlobalSection_comp level c) ≫
      SectionsProjectiveMorphism.sectionProjectiveMorphism A.scheme.hom E.sections E.covers = q := by
  let x : Over.mk (𝟙 S) ⟶ A.scheme :=
    Over.homMk (A.fullLevelGlobalSection level c) (A.fullLevelGlobalSection_comp level c)
  exact (congrArg (fun f => x ≫ f) E.embedding_eq.symm).trans h

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

local notation "M[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "F[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "P[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalPresentation R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "c[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationMarkedPoints.StableHilbertPolarization.toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ

/-- The actual embedding line is a graph power: the prescribed zero
mark trivializes its fiber at the identity. -/
def universalPresentation_rawPowerIso (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    (P[j]).ampleLineBundle.sheaf ≅ ((F[j]).graphBundle.tensorPower d).sheaf := by
  let z := labels.symm 1
  let v := Stable.BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j M[j] c[j] z
  let hv := Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedVectors_cover R i j M[j] c[j] z
  have hz : Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M[j]).left))
      (F[j]).abelian (F[j]).level P[j] 1 = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv := by
    simpa only [z, Equiv.apply_symm_apply] using
      PolarizationMarkedPoints.StableHilbertPolarization.universalPresentation_scalarMark R i j D H hH g Hm Hi N labels qR d hd δ hδ z
  let h := (Quotient.exact
    (PolarizationFrameCoverage.StableHilbertPolarization.universalPresentation_normalizedPowerClass R i j D H hH g Hm Hi N labels qR d hd δ hδ)).some
  exact (F[j]).rawGraphPowerIso_of_scalarZero P[j] d h v hv hz

def graphSections (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    (P[j]).SectionData ((F[j]).graphBundle.tensorPower d) :=
  (P[j]).canonicalSectionData.ofBundleIso
    (universalPresentation_rawPowerIso R i D H hH g Hm Hi N labels qR d hd δ hδ j)

theorem graphSections_geometricallyComplete
    (hg : 0 < g) (hN : 3 ≤ N)
    (hd_eq : d = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (hn : n + 1 = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily (F[j]).abelian.scheme.hom
      ((F[j]).graphBundle.tensorPower d).sheaf
      (graphSections R i D H hH g Hm Hi N labels qR d hd δ hδ j).sections (𝟙 (M[j]).left) :=
  (PolarizationCompleteness.StableHilbertPolarization.universalPresentation_geometricallyComplete R i j D H hH g Hm Hi N labels qR d hd δ hδ
    hg hN hd_eq hn).bundleIso (F[j]).abelian.scheme.hom (P[j]).canonicalSectionData.sections
      (𝟙 (M[j]).left)
      (universalPresentation_rawPowerIso R i D H hH g Hm Hi N labels qR d hd δ hδ j)

def graphSectionsAt (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))} (a : T ⟶ M[j]) :
    ((P[j]).baseChange a.left).SectionData (((F[j]).pullback a.left).graphBundle.tensorPower d) :=
  ((graphSections R i D H hH g Hm Hi N labels qR d hd δ hδ j).baseChangePowers a.left).ofBundleIso
    ((TensorPower.Maps.tensorPowerFunctor ((F[j]).pullback a.left).abelian.scheme.left d).mapIso
      ((F[j]).graphBundle_baseChangeIso a.left).symm)

/-- An actual coefficient basis on an affine Noetherian test. -/
def graphSectionsAt_completeData
    (hg : 0 < g) (hN : 3 ≤ N)
    (hd_eq : d = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (hn : n + 1 = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))} [IsAffine T.left] [IsLocallyNoetherian T.left]
    (a : T ⟶ M[j]) :
    (graphSectionsAt R i D H hH g Hm Hi N labels qR d hd δ hδ j a).CompleteData := by
  let E := graphSections R i D H hH g Hm Hi N labels qR d hd δ hδ j
  let C := E.completeBaseChangeOfGeometric
    (graphSections_geometricallyComplete R i D H hH g Hm Hi N labels qR d hd δ hδ
      hg hN hd_eq hn j) a.left
  exact (C.ofBundleIso
    (M := ((F[j]).graphBundle.pullback (pullback.fst (F[j]).abelian.scheme.hom a.left)).tensorPower d)
    ((F[j]).graphBundle.powerBaseChangeIso
    (pullback.fst (F[j]).abelian.scheme.hom a.left) d)).ofBundleIso
      (M := ((F[j]).pullback a.left).graphBundle.tensorPower d)
      ((TensorPower.Maps.tensorPowerFunctor ((F[j]).pullback a.left).abelian.scheme.left d).mapIso
        ((F[j]).graphBundle_baseChangeIso a.left).symm)

theorem graphSectionsAt_markedPoint (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))} (a : T ⟶ M[j]) (k : Fin m) :
    Over.homMk (((F[j]).pullback a.left).abelian.fullLevelGlobalSection
        ((F[j]).pullback a.left).level (labels k))
      (((F[j]).pullback a.left).abelian.fullLevelGlobalSection_comp
        ((F[j]).pullback a.left).level (labels k)) ≫
      SectionsProjectiveMorphism.sectionProjectiveMorphism ((F[j]).pullback a.left).abelian.scheme.hom
        (graphSectionsAt R i D H hH g Hm Hi N labels qR d hd δ hδ j a).sections
        (graphSectionsAt R i D H hH g Hm Hi N labels qR d hd δ hδ j a).covers =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint
        (Stable.BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j T (a ≫ c[j]) k)
        (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedVectors_cover R i j T (a ≫ c[j]) k) := by
  exact markedSectionData_eq ((F[j]).pullback a.left).abelian
    ((F[j]).pullback a.left).level ((P[j]).baseChange a.left)
    (graphSectionsAt R i D H hH g Hm Hi N labels qR d hd δ hδ j a) (labels k) _
    (PolarizationMarkedPoints.StableHilbertPolarization.universalPresentation_scalarMarkAt R i j D H hH g Hm Hi N labels qR d hd δ hδ a k)

theorem affinePoints_toBalanced_eq_of_iso
    (hg : 0 < g) (hN : 3 ≤ N)
    (hd_eq : d = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (hn : n + 1 = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))} [IsAffine T.left] [IsLocallyNoetherian T.left]
    (a : T ⟶ M[j]) (b : T ⟶ M[k])
    (e : Moduli.Isomorphisms.LevelPreservingIso ((F[j]).pullback a.left) ((F[k]).pullback b.left)) :
    (a ≫ c[j]) ≫ Stable.RankChartsOverBase.stableBalancedAffineChartOverMap R i j =
      (b ≫ c[k]) ≫ Stable.RankChartsOverBase.stableBalancedAffineChartOverMap R i k := by
  let E := graphSectionsAt R i D H hH g Hm Hi N labels qR d hd δ hδ j a
  let E₂ := graphSectionsAt R i D H hH g Hm Hi N labels qR d hd δ hδ k b
  let CE := graphSectionsAt_completeData R i D H hH g Hm Hi N labels qR d hd δ hδ
    hg hN hd_eq hn j a
  let CF := graphSectionsAt_completeData R i D H hH g Hm Hi N labels qR d hd δ hδ
    hg hN hd_eq hn k b
  have hE := (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff
    ((F[j]).pullback a.left).abelian.scheme.hom.appTop.hom
    (((F[j]).pullback a.left).graphBundle.tensorPower d).sheaf E.sections).mpr
      ⟨CE.basis, CE.sections_eq.symm⟩
  have hF := (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff
    ((F[k]).pullback b.left).abelian.scheme.hom.appTop.hom
    (((F[k]).pullback b.left).graphBundle.tensorPower d).sheaf E₂.sections).mpr
      ⟨CF.basis, CF.sections_eq.symm⟩
  have horbit := Polarized.MarkedOrbits.completePolarizedMarkedEmbeddings_frameRelated e d n
    E.sections E₂.sections E.covers E₂.covers hE hF labels
    (Stable.BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j T (a ≫ c[j]))
    (Stable.BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i k T (b ≫ c[k]))
    (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedVectors_cover R i j T (a ≫ c[j]))
    (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedVectors_cover R i k T (b ≫ c[k]))
    (graphSectionsAt_markedPoint R i D H hH g Hm Hi N labels qR d hd δ hδ j a)
    (graphSectionsAt_markedPoint R i D H hH g Hm Hi N labels qR d hd δ hδ k b)
  exact Stable.BalancedOrbitEquality.StableHilbertCoverage.points_toBalanced_eq_of_frameRelated
    R i j k T (a ≫ c[j]) (b ≫ c[k]) horbit

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationCoordinateOrbits.StableHilbertPolarization
