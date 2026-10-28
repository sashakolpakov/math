import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.Algebra.Module.Star

/-! # CM Mixed Hermitian Form -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMMixedHermitianForm

noncomputable section

/-! The original Hermitian matrix acts directly on the actual CM
mixed embedding space. Its real bilinear map evaluates on original
vectors to the mixed embedding of the original Hermitian value. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmMixedEmbedding_conjugation (a : E) :
    mixedEmbedding E (IsCMField.complexConj E a) = star (mixedEmbedding E a) := by
  apply Prod.ext
  · funext w
    exact ((InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w.val)) w.property).elim
  · funext w
    exact IsCMField.complexEmbedding_complexConj E w.val.embedding a

local notation "A" => mixedSpace E
local notation "V" => Fin 3 → A

def cmMixedHermitianForm (H : Matrix (Fin 3) (Fin 3) E) :
    V →ₗ[ℝ] V →ₗ[ℝ] A :=
  ((Matrix.toBilin' (H.map (mixedEmbedding E))).restrictScalars₁₂ ℝ ℝ).compl₁₂
    LinearMap.id (starL' ℝ : V ≃L[ℝ] V).toLinearMap

omit [NumberField E] [IsCMField E] in
theorem cmMixedHermitianForm_apply (H : Matrix (Fin 3) (Fin 3) E) (v w : V) :
    cmMixedHermitianForm H v w =
      ∑ i, ∑ j, v i * mixedEmbedding E (H i j) * star (w j) := by
  change Matrix.toBilin' (H.map (mixedEmbedding E)) v (star w) = _
  rw [Matrix.toBilin'_apply]
  rfl

theorem cmMixedHermitianForm_embedding (H : Matrix (Fin 3) (Fin 3) E) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    cmMixedHermitianForm H (fun i => mixedEmbedding E (v i)) (fun i => mixedEmbedding E (w i)) =
      mixedEmbedding E (Datum.RankThreePELDatum.matrixHermitian H v w) := by
  rw [cmMixedHermitianForm_apply]
  simp only [Datum.RankThreePELDatum.matrixHermitian, map_sum, map_mul, cmMixedEmbedding_conjugation]

omit [NumberField E] [IsCMField E] in
theorem continuous_cmMixedHermitianForm (H : Matrix (Fin 3) (Fin 3) E) :
    Continuous (fun p : V × V => cmMixedHermitianForm H p.1 p.2) := by
  simp only [cmMixedHermitianForm_apply]
  fun_prop

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMMixedHermitianForm
