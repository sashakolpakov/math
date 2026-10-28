import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Units -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Units.CM

noncomputable section

/-! Construct a finite adelic unit from nonzero local coordinates and
integrality of their inverses at almost all places. -/

open Filter OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

def inverse (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hi : ∀ᶠ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace in cofinite, (a v)⁻¹ ∈ v.adicCompletionIntegers ℚ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  ⟨fun v => (a v)⁻¹, hi⟩

def unit (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hn : ∀ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, a v ≠ 0)
    (hi : ∀ᶠ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace in cofinite, (a v)⁻¹ ∈ v.adicCompletionIntegers ℚ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQfˣ where
  val := a
  inv := inverse a hi
  val_inv := by
    apply DFunLike.ext
    intro v
    exact mul_inv_cancel₀ (hn v)
  inv_val := by
    apply DFunLike.ext
    intro v
    exact inv_mul_cancel₀ (hn v)

theorem isUnit_of_local (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hn : ∀ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, a v ≠ 0)
    (hi : ∀ᶠ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace in cofinite, (a v)⁻¹ ∈ v.adicCompletionIntegers ℚ) : IsUnit a :=
  ⟨unit a hn hi, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Units.CM
