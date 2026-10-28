import OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoPurity
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FlasqueComparison

/-! # Complement Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.ComplementPurity

noncomputable section

/-! Purity and the canonical section comparison for the complement of any
nonempty algebraic open in an integral smooth projective presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (R : X.carrier.Opens) [Nonempty R]

/-- A stratum in the complement of a nonempty open has strictly smaller dimension. -/
theorem complementPiece_dimension (P : Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.structureMap)
    (hP : P.support ⊆ R.compl) :
    P.dimension + 1 ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap := by
  rw [P.dimension_eq_closure]
  let T : IrreducibleCloseds X.carrier :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.carrier, isClosed_univ⟩
  have hclosure : (P.closureSupport : Set X.carrier) ⊆ R.compl := closure_minimal hP R.compl.isClosed
  have hPT : P.closureSupport < T := by
    apply lt_of_le_not_ge (Set.subset_univ _)
    intro hTP
    obtain ⟨y⟩ := ‹Nonempty R›
    exact hclosure (hTP (Set.mem_univ y.val)) y.property
  exact (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt P.closureSupport T X.structureMap hPT).trans_le
    (Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le T X.structureMap)

theorem complementLayer_dimension
    (i : Fin (DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl).analyticSupportList.length) :
    ((DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl).analyticFiltrationPiece i).complexDimension + 1 ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap := by
  rw [Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
  apply complementPiece_dimension X R
  exact (Geometric.IntegralSmoothStratification.support_subset_integralSmoothPiecesSupport
    ((DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl).analyticFiltrationPiece_mem i)).trans
    (le_of_eq (DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl).cover)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.structureMap) → ℂ

local instance : Smooth X.structureMap := X.smooth

local instance : ChartedSpace E (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X.toOver ‹IsIntegral X.carrier› X.smooth

local instance : IsManifold 𝓘(ℂ, E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold X.toOver ‹IsIntegral X.carrier› X.smooth ω

local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) := by
  let V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨X, inferInstance⟩
  exact inferInstanceAs (MetrizableSpace V.analyticSpace)

local instance : ChartedSpace E (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk X.structureMap) ‹IsIntegral X.carrier› X.smooth

local instance : IsManifold 𝓘(ℂ, E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold (Over.mk X.structureMap) ‹IsIntegral X.carrier› X.smooth ω

local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) := by
  change MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  infer_instance

theorem complementLayer_open_cohomology_isZero
    (i : Fin (DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl).analyticSupportList.length)
    (U : Opens (TopCat.of ((DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl).analyticFiltrationComplement i)))
    (n : ℕ) (hn : n < 2) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer T
        ((DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl).analyticClosedFiltration i.castSucc)
        ((DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl).analyticClosedFiltration i.succ)}ᶜ n) := by
  let S := DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl
  let : MetrizableSpace (S.analyticFiltrationComplement i) := MetrizableSpace.subtype _
  have hdim : n < 2 * (Module.finrank ℂ E -
      Module.finrank ℂ (S.analyticFiltrationPiece i).analyticModel) := by
    rw [Module.finrank_fin_fun, Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_complex_finrank,
      ← Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
    have hd := complementLayer_dimension X R i
    rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.structureMap] at hd
    change (S.analyticFiltrationPiece i).complexDimension + 1 ≤ _ at hd
    omega
  have h := DivisorClass.Chern.Open.ImmersionPurity.closedComplexImmersion_open_supportCohomology_isZero
    (S.analyticFiltrationLayerInclusion i) (S.isClosedEmbedding_analyticFiltrationLayerInclusion i)
    (S.contMDiff_analyticFiltrationLayerInclusion i ω)
    (S.mfderiv_analyticFiltrationLayerInclusion_injective i) U n hdim
  simp only [S.range_analyticFiltrationLayerInclusion i] at h
  exact h

/-- The closed complement has no relative cohomology below degree two on any analytic open. -/
theorem complement_open_cohomology_isZero (U : Opens T) (n : ℕ) (hn : n < 2) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ R.compl}ᶜ n) := by
  let S := DivisorClass.Chern.CodimensionTwoPurity.Construction.codimensionTwoStratification X R.compl
  have h := DivisorClass.Chern.Open.SupportFiltration.closedSupportFiltration_open_isZero T U (ModuleCat.of ℚ ℚ)
    S.analyticSupportList.length S.analyticClosedFiltration S.analyticClosedFiltration_monotone
    S.analyticClosedFiltration_zero n
    (fun i V => complementLayer_open_cohomology_isZero X R i V n hn)
  have hlast := S.analyticClosedFiltration_last
  rw [hlast] at h
  exact h

/-- Stalk vanishing is obtained from the actual neighborhood cohomology colimit. -/
theorem complementSupportedStalk_isZero (x : T) (n : ℕ) (hn : n < 2) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R)) x).homology n) := by
  let F := AlgebraicTopology.Cohomology.Singular.RelativeStalk.relativeNeighborhoodCohomology (ModuleCat.of ℚ ℚ) T
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R : Set T) x n
  have hF : IsZero F := F.isZero (fun U => by
    have h := complement_open_cohomology_isZero X R U.unop.1 n hn
    have he : {y : U.unop.1 | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ R.compl}ᶜ =
        AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R : Set T) U.unop.1 := by
      ext y
      exact not_not
    rw [he] at h
    exact h)
  exact ((colimit.isColimit F).isZero_pt hF).of_iso
    (AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedStalkRelativeCohomologyIso ℚ T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R) x n)

/-- The canonical map to supported cohomology-sheaf sections is invertible. -/
instance complementSectionMap_isIso (U : Opens T) :
    IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R) U 2) := by
  rw [Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap_def]
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R) U
  have := DivisorClass.Chern.Open.FlasqueComparison.rationalFlasqueOpenSectionMap_isIso U
    (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R))
    (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R)) 2
    (fun n hn => Geometric.GlobalSupportPurity.Cycles.rationalSheafComplex_exactAt_of_stalk_isZero _ n
      (fun x => complementSupportedStalk_isZero X R x n hn))
  infer_instance

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.ComplementPurity
