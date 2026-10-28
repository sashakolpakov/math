import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairIntertwiner

/-! # Adelic Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCover.CM

noncomputable section

/-! The actual adelic Schrödinger cover, with unitary genuine action,
Heisenberg covariance, and exact two-fold kernel all proved. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM

theorem project_negOne (n : ℕ) : ConstructedAdelicGroup.CM.projection n (ConstructedAdelicGroup.CM.negOne n) = 1 :=
  Adelic.PairDecomposition.CM.Kernel.project_negOne _ _

theorem unitary (n : ℕ) (a : ConstructedAdelicGroup.CM.AdelicGroup n) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) :
    (∫ x, (ConstructedAdelicGroup.CM.action n a f).val x * star ((ConstructedAdelicGroup.CM.action n a h).val x)
      ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (FiniteMeasure.CM.measure (Fin n))) =
    ∫ x, f.val x * star (h.val x) ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (FiniteMeasure.CM.measure (Fin n)) :=
  Adelic.PairUnitary.CM.unitary _ _ _ a f h

theorem intertwines (n : ℕ) (a : ConstructedAdelicGroup.CM.AdelicGroup n) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg AdelicCharacter.CM.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n))
      (ConstructedAdelicGroup.CM.projection n a) (ConstructedAdelicGroup.CM.action n a) := Adelic.PairIntertwiner.CM.intertwines n _ _ a

def adelicCover (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ AdelicCharacter.CM.character
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (FiniteMeasure.CM.measure (Fin n))) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (ConstructedAdelicGroup.CM.AdelicGroup n) where
  project := ConstructedAdelicGroup.CM.projection n
  action := ConstructedAdelicGroup.CM.action n
  surjective := ConstructedAdelicGroup.CM.projection_surjective n
  negOne := ConstructedAdelicGroup.CM.negOne n
  negOne_ne_one := ConstructedAdelicGroup.CM.negOne_ne_one n
  project_negOne := CM.project_negOne n
  kernel := ConstructedAdelicGroup.CM.kernel n
  genuine := ConstructedAdelicGroup.CM.genuine n
  faithful := ConstructedAdelicGroup.CM.faithful n
  intertwines := CM.intertwines n
  unitary := CM.unitary n

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCover.CM
