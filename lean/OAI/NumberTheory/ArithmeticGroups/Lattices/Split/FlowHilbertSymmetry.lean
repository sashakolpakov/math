import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingSplitFlow

/-! # Flow Hilbert Symmetry -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FlowHilbertSymmetry.Construction

noncomputable section

/-! Split conjugation is symmetric for the Hilbert--Schmidt inner
product, expressed through Euclidean endomorphism coordinates. -/

open NormedSpace
open scoped Classical

theorem split_conjugation_euclidean_inner
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (t : ℝ) (X Y : L →L[ℝ] L) :
    inner ℝ (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis (exp ((-t) • H) * X * exp (t • H)))
      (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis Y) =
    inner ℝ (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis X)
      (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis (exp ((-t) • H) * Y * exp (t • H))) := by
  change (∑ p : Fin m × Fin m, EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis Y p *
      EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis (exp ((-t) • H) * X * exp (t • H)) p) =
    ∑ p : Fin m × Fin m,
      EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis (exp ((-t) • H) * Y * exp (t • H)) p *
      EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis X p
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ _
  simp only [EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates_apply, Module.Basis.equivFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis]
  rw [Weight.ConjugationCoordinates.Construction.split_exponential_conjugation_coordinate b H hH w heig,
    Weight.ConjugationCoordinates.Construction.split_exponential_conjugation_coordinate b H hH w heig]
  ring

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FlowHilbertSymmetry.Construction
