import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.MatrixUnits
import OAI.AlgebraicGeometry.Comparison.Betti.MatrixFrameBasis

/-! # Local Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalFrames

noncomputable section

/-! A holomorphic family that is a basis at one point gives an actual module basis nearby. -/

open _root_.TopologicalSpace

variable {E F ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [Fintype ι] [DecidableEq ι]
  {U V : Opens E}

def holomorphicSectionFrameMatrix (U : Opens E) (b : Module.Basis ι ℂ F)
    (a : ι → CoefficientMem.holomorphicSections U F) : Matrix ι ι (FunctionPure.holomorphicFunctions U) :=
  fun i j => SectionFrames.holomorphicSectionsBasisEquiv U b (a j) i

omit [DecidableEq ι] in
theorem holomorphicSectionFrameMatrix_restrict (h : V ≤ U) (b : Module.Basis ι ℂ F)
    (a : ι → CoefficientMem.holomorphicSections U F) :
    holomorphicSectionFrameMatrix V b (fun j => Restrictions.holomorphicSectionRestrict h (a j)) =
      (holomorphicSectionFrameMatrix U b a).map (Restrictions.holomorphicFunctionRestrict h) := rfl

def holomorphicSectionBasisOfMatrixUnit (b : Module.Basis ι ℂ F)
    (a : ι → CoefficientMem.holomorphicSections U F) (h : IsUnit (holomorphicSectionFrameMatrix U b a)) :
    Module.Basis ι (FunctionPure.holomorphicFunctions U) (CoefficientMem.holomorphicSections U F) :=
  (MatrixFrameBasis.LinearAlgebra.basisOfUnitMatrix (holomorphicSectionFrameMatrix U b a) h).map
    (SectionFrames.holomorphicSectionsBasisEquiv U b).symm

theorem holomorphicSectionBasisOfMatrixUnit_apply (b : Module.Basis ι ℂ F)
    (a : ι → CoefficientMem.holomorphicSections U F) (h : IsUnit (holomorphicSectionFrameMatrix U b a)) (j : ι) :
    holomorphicSectionBasisOfMatrixUnit b a h j = a j := by
  apply (SectionFrames.holomorphicSectionsBasisEquiv U b).injective
  change SectionFrames.holomorphicSectionsBasisEquiv U b
    ((SectionFrames.holomorphicSectionsBasisEquiv U b).symm
      (MatrixFrameBasis.LinearAlgebra.basisOfUnitMatrix (holomorphicSectionFrameMatrix U b a) h j)) = _
  rw [LinearEquiv.apply_symm_apply]
  funext i
  exact MatrixFrameBasis.LinearAlgebra.basisOfUnitMatrix_apply _ h i j

theorem exists_holomorphicSection_localBasis (b : Module.Basis ι ℂ F)
    (a : ι → CoefficientMem.holomorphicSections U F) (x : U)
    (hx : LinearIndependent ℂ (fun j => (a j).val x)) :
    ∃ (V : Opens E) (h : V ≤ U), (x : E) ∈ V ∧
      ∃ c : Module.Basis ι (FunctionPure.holomorphicFunctions V) (CoefficientMem.holomorphicSections V F),
        ∀ j, c j = Restrictions.holomorphicSectionRestrict h (a j) := by
  let A := holomorphicSectionFrameMatrix U b a
  have hi : LinearIndependent ℂ ((A.map (MatrixUnits.holomorphicFunctionEvaluation x)).col) :=
    hx.map' b.equivFun.toLinearMap (LinearMap.ker_eq_bot.mpr b.equivFun.injective)
  have hd : (A.map (MatrixUnits.holomorphicFunctionEvaluation x)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hi)).ne_zero
  obtain ⟨V, h, hxV, hA⟩ := MatrixUnits.exists_restrict_holomorphicMatrix_isUnit A x hd
  have hB : IsUnit
      (holomorphicSectionFrameMatrix V b (fun j => Restrictions.holomorphicSectionRestrict h (a j))) := by
    rw [holomorphicSectionFrameMatrix_restrict]
    exact hA
  exact ⟨V, h, hxV, holomorphicSectionBasisOfMatrixUnit b _ hB,
    holomorphicSectionBasisOfMatrixUnit_apply b _ hB⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalFrames
