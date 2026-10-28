import OAI.AlgebraicGeometry.Comparison.Betti.PuncturedParametricDbarPrimitive
import OAI.AlgebraicGeometry.Comparison.Betti.PuncturedDirections

/-! # Punctured Parametric Dbar -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PuncturedParametricDbar.Dolbeault

noncomputable section

section

/-! Preservation of every holomorphic parameter direction by the
actual global primitive on the punctured complex line. -/

open _root_.TopologicalSpace Set _root_.Complex
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem puncturedParametricCauchyCandidate_preserves_direction
    (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)))
    (q : P × ℂ) (hq : q.1 ∈ S) (hz : q.2 ≠ 0) (v : P)
    (hv : ∀ w : ℂ, w ≠ 0 → fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (PuncturedParametricDbarPrimitive.Dolbeault.puncturedParametricCauchyCandidate S g hg) q (I • v, 0) =
      I • fderiv ℝ (PuncturedParametricDbarPrimitive.Dolbeault.puncturedParametricCauchyCandidate S g hg) q (v, 0) := by
  let A := Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput g) (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg)
  let B := Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput g) (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg)
  have hA : ContDiffAt ℝ ∞ A q :=
    (Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_smooth S _ (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg)).contDiffAt
      ((S.isOpen.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩)
  have hB : ContDiffAt ℝ ∞ B (q.1, q.2⁻¹) :=
    (Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_smooth S _ (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg)).contDiffAt
      ((S.isOpen.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩)
  have hBinv : ContDiffAt ℝ ∞ (fun y : P × ℂ => B (y.1, y.2⁻¹)) q :=
    hB.comp q (contDiffAt_fst.prodMk (contDiffAt_snd.inv hz))
  have hAdir : fderiv ℝ A q (I • v, 0) = I • fderiv ℝ A q (v, 0) :=
    Open.ParametricDbarDirections.Dolbeault.openParametricCauchyCandidate_preserves_holomorphic_direction S _
      (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg) q hq v
      (fun w => PuncturedDirections.Dolbeault.puncturedCauchyOuterInput_preserves_direction S g hg (q.1, w) hq v hv)
  have hBdir : fderiv ℝ B (q.1, q.2⁻¹) (I • v, 0) = I • fderiv ℝ B (q.1, q.2⁻¹) (v, 0) :=
    Open.ParametricDbarDirections.Dolbeault.openParametricCauchyCandidate_preserves_holomorphic_direction S _
      (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg) (q.1, q.2⁻¹) hq v
      (fun w => PuncturedDirections.Dolbeault.puncturedCauchyInnerInput_preserves_direction S g hg (q.1, w) hq v hv)
  have hpull : fderiv ℝ (fun y : P × ℂ => B (y.1, y.2⁻¹)) q (I • v, 0) =
      I • fderiv ℝ (fun y : P × ℂ => B (y.1, y.2⁻¹)) q (v, 0) := by
    simpa only [one_smul] using ParameterLinePullbackDerivative.Dolbeault.parameter_direction_line_weight
      (g := B) (a := fun _ => 1) (φ := Inv.inv)
      (by simpa only [one_smul] using hBinv.differentiableAt (by simp))
      (hB.differentiableAt (by simp)) v hBdir
  change fderiv ℝ (fun y => A y + B (y.1, y.2⁻¹)) q (I • v, 0) =
    I • fderiv ℝ (fun y => A y + B (y.1, y.2⁻¹)) q (v, 0)
  rw [fderiv_fun_add (hA.differentiableAt (by simp)) (hBinv.differentiableAt (by simp)),
    add_apply, add_apply, hAdir, hpull, smul_add]

end

section

/-! Preservation of coefficient kernels by the actual punctured-line
primitive, including the input extensions at the added zero point. -/

open _root_.TopologicalSpace Set
open scoped ContDiff

variable {P F G : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] [CompleteSpace G]

theorem puncturedParametricCauchyCandidate_kernel (L : F →L[ℂ] G) (S : Opens P)
    (g : P × ℂ → F) (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)))
    (q : P × ℂ) (hq : q.1 ∈ S)
    (hzero : ∀ w : ℂ, w ≠ 0 → L (g (q.1, w)) = 0) :
    L (PuncturedParametricDbarPrimitive.Dolbeault.puncturedParametricCauchyCandidate S g hg q) = 0 := by
  have houter : ∀ w : ℂ, L (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput g (q.1, w)) = 0 := by
    intro w
    by_cases hw : w = 0
    · subst w
      rw [PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_zero g (by norm_num), map_zero]
    · change L ((1 - (PuncturedCauchy.Dolbeault.puncturedCauchyBump w : ℂ)) • g (q.1, w)) = 0
      rw [map_smul, hzero w hw, smul_zero]
  have hinner : ∀ w : ℂ, L (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput g (q.1, w)) = 0 := by
    intro w
    by_cases hw : w = 0
    · subst w
      rw [PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_zero g (by norm_num), map_zero]
    · change L (PuncturedCauchy.Dolbeault.complexInversionJacobian w • ((PuncturedCauchy.Dolbeault.puncturedCauchyBump w⁻¹ : ℂ) • g (q.1, w⁻¹))) = 0
      rw [map_smul, map_smul, hzero w⁻¹ (inv_ne_zero hw), smul_zero, smul_zero]
  change L (Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S _ (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg) q +
    Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S _ (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg) (q.1, q.2⁻¹)) = 0
  rw [map_add, Open.ParametricDbarKernels.Dolbeault.openParametricCauchyCandidate_kernel L S _ (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg) q hq houter,
    Open.ParametricDbarKernels.Dolbeault.openParametricCauchyCandidate_kernel L S _ (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg) (q.1, q.2⁻¹) hq hinner,
    add_zero]

end

/-! A common actual primitive for ordinary and punctured complex
coordinate lines over any open finite-dimensional complex parameter domain. -/

open _root_.TopologicalSpace Set _root_.Complex
open scoped ContDiff

def cauchyCoordinateOpen : Bool → Opens ℂ
  | false => ⊤
  | true => PuncturedCauchy.Dolbeault.puncturedComplexOpen

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

def coordinateLineCauchyCandidate (S : Opens P) (b : Bool) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (cauchyCoordinateOpen b : Set ℂ))) : P × ℂ → F := by
  cases b
  · exact Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg
  · exact PuncturedParametricDbarPrimitive.Dolbeault.puncturedParametricCauchyCandidate S g hg

theorem coordinateLineCauchyCandidate_smooth (S : Opens P) (b : Bool) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (cauchyCoordinateOpen b : Set ℂ))) :
    ContDiffOn ℝ ∞ (coordinateLineCauchyCandidate S b g hg)
      ((S : Set P) ×ˢ (cauchyCoordinateOpen b : Set ℂ)) := by
  cases b
  · exact Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_smooth S g hg
  · exact PuncturedParametricDbarPrimitive.Dolbeault.puncturedParametricCauchyCandidate_smooth S g hg

theorem coordinateLineCauchyCandidate_dbar (S : Opens P) (b : Bool) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (cauchyCoordinateOpen b : Set ℂ)))
    {p : P} (hp : p ∈ S) {z : ℂ} (hz : z ∈ cauchyCoordinateOpen b) :
    VectorDbar.Dolbeault.vectorDbar (fun w => coordinateLineCauchyCandidate S b g hg (p, w)) z = g (p, z) := by
  cases b
  · exact Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_dbar S g hg hp z
  · exact PuncturedParametricDbarPrimitive.Dolbeault.puncturedParametricCauchyCandidate_dbar S g hg hp hz

theorem coordinateLineCauchyCandidate_preserves_direction (S : Opens P) (b : Bool) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (cauchyCoordinateOpen b : Set ℂ)))
    (q : P × ℂ) (hq : q ∈ (S : Set P) ×ˢ (cauchyCoordinateOpen b : Set ℂ)) (v : P)
    (hv : ∀ w ∈ cauchyCoordinateOpen b,
      fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (coordinateLineCauchyCandidate S b g hg) q (I • v, 0) =
      I • fderiv ℝ (coordinateLineCauchyCandidate S b g hg) q (v, 0) := by
  cases b
  · exact Open.ParametricDbarDirections.Dolbeault.openParametricCauchyCandidate_preserves_holomorphic_direction S g hg q hq.1 v
      (fun w => hv w (mem_univ _))
  · exact puncturedParametricCauchyCandidate_preserves_direction S g hg q hq.1 hq.2 v hv

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G] [CompleteSpace G]

theorem coordinateLineCauchyCandidate_kernel (L : F →L[ℂ] G) (S : Opens P) (b : Bool) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (cauchyCoordinateOpen b : Set ℂ)))
    (q : P × ℂ) (hq : q.1 ∈ S) (hzero : ∀ w ∈ cauchyCoordinateOpen b, L (g (q.1, w)) = 0) :
    L (coordinateLineCauchyCandidate S b g hg q) = 0 := by
  cases b
  · exact Open.ParametricDbarKernels.Dolbeault.openParametricCauchyCandidate_kernel L S g hg q hq (fun w => hzero w (mem_univ _))
  · exact puncturedParametricCauchyCandidate_kernel L S g hg q hq hzero

end

end OAI.AlgebraicGeometry.Comparison.Betti.PuncturedParametricDbar.Dolbeault
