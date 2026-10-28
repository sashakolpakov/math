import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.SectionCoordinates
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectionEquiv
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscUpdate

/-! # Coordinate Split -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoordinateSplit.Dolbeault

noncomputable section

/-! Splitting one actual coordinate identifies holomorphic sections on a
finite coordinate product with sections on its parameter-times-line domain. -/

open _root_.CategoryTheory _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscUpdate

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ)

def coordinatePolydiscSplitHomeomorph :
    DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W) ≃ₜ
      ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W where
  toFun x := ⟨DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i x.val, DivisorClass.Chern.CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W x.property⟩
  invFun q := ⟨(DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm q.val, DivisorClass.Chern.CoordinatePolydiscUpdate.splitComplexCoordinate_update_symm_mapsTo U i W q.property⟩
  left_inv x := Subtype.ext ((DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm_apply_apply x.val)
  right_inv q := Subtype.ext ((DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).apply_symm_apply q.val)
  continuous_toFun := ((DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem coordinatePolydiscSplitHomeomorph_holomorphic :
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, ({j : ι // j ≠ i} → ℂ) × ℂ) ∞
      (coordinatePolydiscSplitHomeomorph U i W) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap.contMDiff.comp
    (contMDiff_subtype_val (U := DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)))

theorem coordinatePolydiscSplitHomeomorph_symm_holomorphic :
    ContMDiff 𝓘(ℂ, ({j : ι // j ≠ i} → ℂ) × ℂ) 𝓘(ℂ, ι → ℂ) ∞
      (coordinatePolydiscSplitHomeomorph U i W).symm := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap.contMDiff.comp
    (contMDiff_subtype_val
      (U := ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W))

def coordinateHolomorphicSectionEquiv :
    FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)) ≃ₐ[ℂ]
      FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W) :=
  (StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv (ι → ℂ) _).trans
    ((ProjectiveTwist.SectionCoordinates.Dolbeault.holomorphicBiholomorphFunctionEquiv (coordinatePolydiscSplitHomeomorph U i W)
      (coordinatePolydiscSplitHomeomorph_holomorphic U i W)
      (coordinatePolydiscSplitHomeomorph_symm_holomorphic U i W)).trans
        (StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv (({j : ι // j ≠ i} → ℂ) × ℂ) _).symm)

theorem coordinateHolomorphicSectionEquiv_apply
    (f : FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)))
    (q : ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W) :
    (coordinateHolomorphicSectionEquiv U i W f).val q =
      f.val ((coordinatePolydiscSplitHomeomorph U i W).symm q) := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoordinateSplit.Dolbeault
