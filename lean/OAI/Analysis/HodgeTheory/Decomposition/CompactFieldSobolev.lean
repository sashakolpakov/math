import OAI.Analysis.HodgeTheory.Decomposition.SobolevPostcomposition
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Compact Field Sobolev -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CompactFieldSobolev.Constructions

noncomputable section

section

/-! Finite smooth coefficient fields act on actual L² vector functions
and preserve every natural-order native Sobolev space. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap BigOperators
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction

variable {E F G ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [Fintype ι]

def schwartzFiniteFieldL2 (g : ι → 𝓢(E, ℂ)) (L : ι → F →L[ℂ] G) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp G 2 (volume : Measure E) :=
  ∑ i, ((L i).compLpL 2 volume).comp (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (g i))

omit [CompleteSpace F] [CompleteSpace G] in
theorem schwartzFiniteFieldL2_coe (g : ι → 𝓢(E, ℂ)) (L : ι → F →L[ℂ] G)
    (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), schwartzFiniteFieldL2 g L u x = ∑ i, g i x • L i (u x) := by
  have hterm : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      ((L i).compLpL 2 volume (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (g i) u)) x = g i x • L i (u x) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [(L i).coeFn_compLpL (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (g i) u),
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe (g i) u] with x hL hg
    rw [hL, hg, map_smul]
  filter_upwards [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction.lp_coe_finsetSum (fun i => (L i).compLpL 2 volume (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (g i) u)) Finset.univ,
    hterm] with x hsum hx
  simp only [schwartzFiniteFieldL2, sum_apply, ContinuousLinearMap.comp_apply]
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => hx i)

theorem lp_postcomposition_memSobolev (L : F →L[ℂ] G) {s : ℝ}
    (u : Lp F 2 (volume : Measure E)) (hu : MemSobolev s 2 (u : 𝓢'(E, F))) :
    MemSobolev s 2 (L.compLpL 2 volume u : 𝓢'(E, G)) := by
  have h := SobolevPostcomposition.Constructions.memSobolev_postcomposition L hu
  exact (SobolevPostcomposition.Constructions.distributionPostcomposition_Lp L u) ▸ h

theorem schwartzMultiply_memSobolev (g : 𝓢(E, ℂ)) (n : ℕ)
    (u : Lp F 2 (volume : Measure E)) (hu : MemSobolev (n : ℝ) 2 (u : 𝓢'(E, F))) :
    MemSobolev (n : ℝ) 2 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u : 𝓢'(E, F)) := by
  have h := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.memSobolev_nat_schwartz_cutoff (E := E) (F := F) n g
    (u := (u : 𝓢'(E, F))) hu
  exact (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_distribution g u).symm ▸ h

theorem schwartzFiniteFieldL2_memSobolev (g : ι → 𝓢(E, ℂ)) (L : ι → F →L[ℂ] G)
    (n : ℕ) (u : Lp F 2 (volume : Measure E)) (hu : MemSobolev (n : ℝ) 2 (u : 𝓢'(E, F))) :
    MemSobolev (n : ℝ) 2 (schwartzFiniteFieldL2 g L u : 𝓢'(E, G)) := by
  have hterm (i : ι) : MemSobolev (n : ℝ) 2
      ((L i).compLpL 2 volume (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (g i) u) : 𝓢'(E, G)) :=
    lp_postcomposition_memSobolev (L i) _ (schwartzMultiply_memSobolev (g i) n u hu)
  simp only [schwartzFiniteFieldL2, sum_apply, ContinuousLinearMap.comp_apply]
  have hsum : ((∑ i, (L i).compLpL 2 volume (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (g i) u) : Lp G 2 volume) : 𝓢'(E, G)) =
      ∑ i, ((L i).compLpL 2 volume (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (g i) u) : 𝓢'(E, G)) :=
    map_sum (Lp.toTemperedDistributionCLM (E := E) G volume 2) _ Finset.univ
  rw [hsum]
  exact (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevDistributionSubmodule E G (n : ℝ)).sum_mem (fun i _ => hterm i)

end

/-! Actual compactly supported smooth complex coefficient fields between
finite-dimensional fibers preserve native Sobolev regularity. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff BigOperators
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction

variable {E F G ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [Fintype ι] [Fintype κ]

omit [CompleteSpace F] [CompleteSpace G] in
theorem operator_orthonormal_expansion (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : F →L[ℂ] G) (u : F) :
    (∑ p : ι × κ, inner ℂ (c p.1) (A (b p.2)) •
      InnerProductSpace.rankOne ℂ (c p.1) (b p.2) u) = A u := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ k, inner ℂ (b k) u • A (b k) := by
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = inner ℂ (b k) u • ∑ j, inner ℂ (c j) (A (b k)) • c j := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro j _
          change inner ℂ (c j) (A (b k)) • (inner ℂ (b k) u • c j) = _
          exact smul_comm _ _ _
        _ = _ := congrArg (fun v => inner ℂ (b k) u • v) (c.sum_repr' (A (b k)))
    _ = A (∑ k, inner ℂ (b k) u • b k) := by simp only [map_sum, map_smul]
    _ = A u := congrArg A (b.sum_repr' u)

def compactSmoothFieldCoefficient (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℂ] G) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (p : ι × κ) : 𝓢(E, ℂ) := by
  have hq : HasCompactSupport (fun x => inner ℂ (c p.1) (A x (b p.2))) :=
    hAc.comp_left (g := fun T : F →L[ℂ] G => inner ℂ (c p.1) (T (b p.2))) (by simp)
  have hAv : ContDiff ℝ ∞ (fun x => A x (b p.2)) :=
    ((ContinuousLinearMap.apply ℂ G (b p.2)).restrictScalars ℝ).contDiff.comp hA
  have hqsmooth : ContDiff ℝ ∞ (fun x => inner ℂ (c p.1) (A x (b p.2))) :=
    ((innerSL ℂ (c p.1)).contDiff.restrict_scalars ℝ).comp hAv
  exact hq.toSchwartzMap hqsmooth

def compactSmoothFieldL2 (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℂ] G) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp G 2 (volume : Measure E) :=
  schwartzFiniteFieldL2 (compactSmoothFieldCoefficient b c A hA hAc)
    (fun p => InnerProductSpace.rankOne ℂ (c p.1) (b p.2))

omit [CompleteSpace F] [CompleteSpace G] in
theorem compactSmoothFieldL2_coe (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℂ] G) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), compactSmoothFieldL2 b c A hA hAc u x = A x (u x) := by
  filter_upwards [schwartzFiniteFieldL2_coe (compactSmoothFieldCoefficient b c A hA hAc)
    (fun p => InnerProductSpace.rankOne ℂ (c p.1) (b p.2)) u] with x hx
  change schwartzFiniteFieldL2 _ _ u x = _
  rw [hx]
  exact operator_orthonormal_expansion b c (A x) (u x)

theorem compactSmoothFieldL2_memSobolev (b : OrthonormalBasis κ ℂ F) (c : OrthonormalBasis ι ℂ G)
    (A : E → F →L[ℂ] G) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (n : ℕ) (u : Lp F 2 (volume : Measure E)) (hu : MemSobolev (n : ℝ) 2 (u : 𝓢'(E, F))) :
    MemSobolev (n : ℝ) 2 (compactSmoothFieldL2 b c A hA hAc u : 𝓢'(E, G)) :=
  schwartzFiniteFieldL2_memSobolev _ _ n u hu

end

end OAI.Analysis.HodgeTheory.Decomposition.CompactFieldSobolev.Constructions
