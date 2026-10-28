import OAI.RepresentationTheory.Hecke.RadialDilation.PrimePairing
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteConjugation

/-! # Prime Matrix Action -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PrimeMatrixAction.Realization

noncomputable section

/-! One-prime symplectic matrices act on the full local coordinate and fix the away coordinate. -/

open scoped Classical _root_.Matrix
open _root_.Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem finitePrimeMatrix_fixes_zero_coordinate (v : HeightOneSpectrum ℤ)
    (A : Matrix κ κ (v.adicCompletion ℚ)) (x : κ → Theta.PoissonAutomorphyNormalizationData.AQf)
    (hx : (fun i => FiniteSchur.Realization.finitePrimeEval v (x i)) = 0) : FiniteConjugation.Realization.finitePrimeMatrix v A *ᵥ x = x := by
  funext i
  apply DFunLike.ext
  intro w
  change FiniteSchur.Realization.finitePrimeEval w ((FiniteConjugation.Realization.finitePrimeMatrix v A *ᵥ x) i) = FiniteSchur.Realization.finitePrimeEval w (x i)
  rw [RingHom.map_mulVec]
  by_cases hw : w = v
  · subst w
    rw [FiniteConjugation.Realization.finitePrimeMatrix_eval_same]
    change (A *ᵥ (fun j => FiniteSchur.Realization.finitePrimeEval v (x j))) i = FiniteSchur.Realization.finitePrimeEval v (x i)
    rw [hx, Matrix.mulVec_zero]
    exact (congrFun hx i).symm
  · rw [FiniteConjugation.Realization.finitePrimeMatrix_eval_other v w hw, Matrix.one_mulVec]
    rfl

variable (q : ℕ) [Fact q.Prime]

omit [Fintype κ] [DecidableEq κ] in
theorem fullPrimeAway_zero_coordinate (y : PrimeChart.Realization.FullPrimeAwayPosition q (ι := κ)) :
    (fun i => FiniteSchur.Realization.finitePrimeEval (FiniteSchur.Realization.rationalPrime q) (y.val i)) = 0 := by
  funext i
  have h := congrFun y.property i
  change (FiniteSchur.Realization.padicCoordinateEquiv q).symm (FiniteSchur.Realization.finitePrimeEval (FiniteSchur.Realization.rationalPrime q) (y.val i)) = 0 at h
  apply (FiniteSchur.Realization.padicCoordinateEquiv q).symm.injective
  change (FiniteSchur.Realization.padicCoordinateEquiv q).symm (FiniteSchur.Realization.finitePrimeEval (FiniteSchur.Realization.rationalPrime q) (y.val i)) =
    (FiniteSchur.Realization.padicCoordinateEquiv q).symm 0
  rw [h, map_zero]

omit [DecidableEq κ] in
theorem fullPrime_matrix_inclusion (A : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) (x : κ → ℚ_[q]) :
    A *ᵥ PrimeChart.Realization.fullPrimeInclusion q x = PrimeChart.Realization.fullPrimeInclusion q (A.map (FiniteSchur.Realization.finitePadicProjection q) *ᵥ x) := by
  exact MatrixProjection.Realization.matrix_mul_projected_vector (FiniteSchur.Realization.finitePadicProjection q).toRingHom
    (FiniteSchur.Realization.finitePadicInclusion q).toAddMonoidHom (FinitePhaseProjection.Realization.finitePadic_mul_inclusion q) A x

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_symplectic_fixes_away (g : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q])
    (y : PrimeChart.Realization.FullPrimeAwayPosition q (ι := Sum ι ι)) :
    (FiniteConjugation.Realization.finitePadicSymplecticInclusion q g).val *ᵥ y.val = y.val := by
  exact finitePrimeMatrix_fixes_zero_coordinate (FiniteSchur.Realization.rationalPrime q)
    (g.val.map (FiniteSchur.Realization.padicCoordinateEquiv q)) y.val (fullPrimeAway_zero_coordinate q y)

theorem fullPrime_symplectic_action (g : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q]) (x : Sum ι ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (FiniteConjugation.Realization.finitePadicSymplecticInclusion q g).val *ᵥ x =
      PrimeChart.Realization.fullPrimeInclusion q (g.val *ᵥ PrimeChart.Realization.fullPrimeProjection q x) + (PrimeChart.Realization.fullPrimeAway q x).val := by
  have hp : (FiniteConjugation.Realization.finitePadicSymplecticInclusion q g).val.map (FiniteSchur.Realization.finitePadicProjection q) = g.val :=
    congrArg Subtype.val (FiniteConjugation.Realization.finitePadicSymplecticInclusion_projection q g)
  calc
    _ = (FiniteConjugation.Realization.finitePadicSymplecticInclusion q g).val *ᵥ
        (PrimeChart.Realization.fullPrimeInclusion q (PrimeChart.Realization.fullPrimeProjection q x) + (PrimeChart.Realization.fullPrimeAway q x).val) := by
      rw [PrimeChart.Realization.fullPrime_decomposition]
    _ = _ := by
      rw [Matrix.mulVec_add, fullPrime_matrix_inclusion, hp, fullPrime_symplectic_fixes_away]

theorem fullPrime_symplectic_projection (g : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q]) (x : Sum ι ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeChart.Realization.fullPrimeProjection q ((FiniteConjugation.Realization.finitePadicSymplecticInclusion q g).val *ᵥ x) =
      g.val *ᵥ PrimeChart.Realization.fullPrimeProjection q x := by
  rw [fullPrime_symplectic_action, map_add, PrimeChart.Realization.fullPrimeProjection_inclusion,
    show PrimeChart.Realization.fullPrimeProjection q (PrimeChart.Realization.fullPrimeAway q x).val = 0 from (PrimeChart.Realization.fullPrimeAway q x).property, add_zero]

theorem fullPrime_symplectic_away (g : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q]) (x : Sum ι ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeChart.Realization.fullPrimeAway q ((FiniteConjugation.Realization.finitePadicSymplecticInclusion q g).val *ᵥ x) = PrimeChart.Realization.fullPrimeAway q x := by
  rw [fullPrime_symplectic_action, map_add, PrimeChart.Realization.fullPrimeAway_inclusion, PrimeChart.Realization.fullPrimeAway_kernel, zero_add]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PrimeMatrixAction.Realization
