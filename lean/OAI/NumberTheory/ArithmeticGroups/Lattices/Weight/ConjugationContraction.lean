import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ConjugationCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationNilpotence

/-! # Conjugation Contraction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ConjugationContraction.Construction

noncomputable section

/-! The negative regular split flow contracts every weight-raising
operator to zero and preserves the weight-raising subspace. -/

open scoped _root_.Topology
open Filter NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem split_conjugation_preserves_weightRaising
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (t : ℝ) (X : L →L[ℝ] L) (hX : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    exp ((-t) • H) * X * exp (t • H) ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w := by
  intro i j hij
  rw [ConjugationCoordinates.Construction.split_exponential_conjugation_coordinate b H hH w heig, hX i j hij, mul_zero]

theorem split_conjugation_contracts_weightRaising
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (X : L →L[ℝ] L) (hX : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    Tendsto (fun t : ℝ => exp ((-t) • H) * X * exp (t • H)) atTop (𝓝 0) := by
  let e := (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis).trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m × Fin m => ℝ))
  apply e.toHomeomorph.isEmbedding.tendsto_nhds_iff.mpr
  change Tendsto (fun t : ℝ => e (exp ((-t) • H) * X * exp (t • H))) atTop (𝓝 (e 0))
  rw [e.map_zero]
  apply tendsto_pi_nhds.mpr
  intro p
  have he (t : ℝ) : e (exp ((-t) • H) * X * exp (t • H)) p =
      Real.exp (t * (w p.1 - w p.2)) * b.repr (X (b p.1)) p.2 := by
    change b.toBasis.equivFun ((exp ((-t) • H) * X * exp (t • H)) (b p.1)) p.2 = _
    rw [Module.Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    exact ConjugationCoordinates.Construction.split_exponential_conjugation_coordinate b H hH w heig t X p.2 p.1
  change Tendsto (fun t => e (exp ((-t) • H) * X * exp (t • H)) p) atTop (𝓝 0)
  simp_rw [he]
  by_cases hp : w p.2 ≤ w p.1
  · simp only [hX p.2 p.1 hp, mul_zero]
    exact tendsto_const_nhds
  · have hneg : w p.1 - w p.2 < 0 := sub_neg.mpr (lt_of_not_ge hp)
    have ht := Real.tendsto_exp_atBot.comp (Filter.Tendsto.atTop_mul_const_of_neg hneg tendsto_id)
    simpa only [Function.comp_apply, id_eq, zero_mul] using! ht.mul_const (b.repr (X (b p.1)) p.2)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ConjugationContraction.Construction
