import OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedHolomorphicSurjectivity
import OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedOpenSectionBases
import OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothExteriorRank
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartOpenRank
import OAI.AlgebraicGeometry.Comparison.Betti.EqualRankSurjectivity
import OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafLocalIso

/-! # Holomorphic Module Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HolomorphicModuleIso

noncomputable section

/-! The actual analytified differential-module comparison is an isomorphism in every degree on smooth integral schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartOpenRank

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem analytifiedComparison_localBijective (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (p : O) (n : ℕ) :
    ∃ W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X), W ≤ O ∧ (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ∈ W ∧
      Function.Bijective ((AnalytifiedForm.analytifiedExteriorToHolomorphicModuleMap X n).val.app (op W)) := by
  let x := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  let U := ExteriorFrames.standardSmoothChart X x
  have hxU : x ∈ U := (ExteriorFrames.standardSmoothChart_spec X x).1
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : IsAffine (Open.AffineIsoEvaluation.openOver X U).left := ExteriorFrames.standardSmoothChart_affine X x
  let : Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) :=
    ExteriorFrames.standardSmoothChart_standardSmooth X x
  let e := chartAt (RegularSmoothness.NativeModel X) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have he : e ∈ atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := chart_mem_atlas _ _
  let V : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := (O ⊓ Open.AffineIsoEvaluation.analyticOpen X U) ⊓ ⟨e.source, e.open_source⟩
  have hpV : (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ∈ V := ⟨⟨p.property, hxU⟩, mem_chart_source _ _⟩
  obtain ⟨W, hWV, hpW, hs⟩ := AnalytifiedHolomorphicSurjectivity.analytifiedExteriorToHolomorphicModuleMap_localSurjective X V ⟨p, hpV⟩ n
  have hW : (W : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ e.source := fun _ hx => (hWV hx).2
  have hWU : W ≤ Open.AffineIsoEvaluation.analyticOpen X U := fun _ hx => (hWV hx).1.2
  let : Module C^∞⟮𝓘(ℂ, RegularSmoothness.NativeModel X), W; 𝓘(ℂ), ℂ⟯
      (((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.obj (op W)) :=
    inferInstanceAs (Module ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj (op W))
      (((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)).val.obj (op W)))
  let b := AnalytifiedOpenSectionBases.standardSmoothOpenAnalytifiedSectionBasis X U n W hWU
  let c := Holomorphic.ChartOpenRank.chartContainedFormBasis e he W hW n
  have hd : Module.finrank ℂ (RegularSmoothness.NativeModel X) = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
    simp [RegularSmoothness.NativeModel]
  have hcard : Nat.card (ExteriorFrames.exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X U) n) =
      Nat.card (Fin (Module.finrank ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule (RegularSmoothness.NativeModel X) n 0))) := by
    rw [Holomorphic.ChartOpenRank.chartContainedFormBasis_card, hd]
    exact StandardSmoothExteriorRank.standardSmooth_openExteriorFrameIndex_card X U n
  have hi := EqualRankSurjectivity.LinearAlgebra.injective_of_surjective_of_basis_card
    (R := C^∞⟮𝓘(ℂ, RegularSmoothness.NativeModel X), W; 𝓘(ℂ), ℂ⟯) b c hcard
      ((AnalytifiedForm.analytifiedExteriorToHolomorphicModuleMap X n).val.app (op W)).hom hs
  exact ⟨W, (hWV.trans inf_le_left).trans inf_le_left, hpW, hi, hs⟩

theorem analytifiedExteriorToHolomorphicModuleMap_isIso (n : ℕ) :
    IsIso (AnalytifiedForm.analytifiedExteriorToHolomorphicModuleMap X n) :=
  Betti.Module.SheafLocalIso.RingedModules.moduleSheaf_isIso_of_localBijective _
    (fun O p => analytifiedComparison_localBijective X O p n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HolomorphicModuleIso
