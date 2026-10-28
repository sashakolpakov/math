import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Fourier
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Linear
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.CoverNormalization

/-! # Weil Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.WeilData.CM

noncomputable section

/-! Existence of the full PoissonAutomorphy Weil data, constructed from the actual
real, finite, and adelic covers and the proved rational generator laws.
No representation data, rational splitting, or theta invariance is an input. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM

def weilData (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin n) (ConstructedAdelicGroup.CM.RealGroup n) (ConstructedAdelicGroup.CM.FiniteGroup n) (ConstructedAdelicGroup.CM.AdelicGroup n) where
  character := AdelicCharacter.CM.character
  character_continuous := AdelicCharacter.CM.character_continuous
  character_unitary := AdelicCharacter.CM.character_unitary
  character_rational := AdelicCharacter.CM.character_rational
  character_real := AdelicCharacter.CM.character_real
  finiteCharacter := AdelicCharacter.CM.Finite.character
  finiteCharacter_eq := fun t => (AdelicCharacter.CM.character_finite t).symm
  finiteMeasure := FiniteMeasure.CM.measure (Fin n)
  finiteMeasure_haar := FiniteMeasure.CM.measure_haar (Fin n)
  finiteMeasure_selfDual := Finite.FourierHeisenberg.CM.Inversion.self_dual
  real := RealCover.CM.realCover n
  finite := Finite.ConstructedCover.CM.finiteCover (Fin n)
  adelic := AdelicCover.CM.adelicCover n
  includeReal := ConstructedAdelicGroup.CM.includeReal n
  includeFinite := ConstructedAdelicGroup.CM.includeFinite n
  commute := ConstructedAdelicGroup.CM.commute n
  factorization := Adelic.AdelicPairGroup.CM.factorization _ _
  includeReal_covers := Adelic.PairDecomposition.CM.includeReal_covers _ _
  includeFinite_covers := Adelic.PairDecomposition.CM.includeFinite_covers _ _
  centralProduct_kernel := ConstructedAdelicGroup.CM.centralProduct_kernel n
  decompose := ConstructedAdelicGroup.CM.decompose n
  rationalSplit := Rational.Split.CM.split n
  rationalSplit_covers := Rational.Split.CM.split_covers n
  rational_linear := Rational.Linear.CM.rational_linear n
  rational_quadratic := Rational.Split.CM.rational_quadratic n
  rational_fourier := Rational.Fourier.CM.rational_fourier n
  vacuum := Vacuum.CM.vacuum (Fin n)
  vacuum_eq := Vacuum.CM.vacuum_apply (Fin n)
  real_normalization := Real.CoverNormalization.CM.real_normalization n

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.WeilData.CM
