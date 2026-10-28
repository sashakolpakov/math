import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TensorRepresentatives
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum

/-! # Integral Coordinate Vacuum -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralCoordinateVacuum.CM

noncomputable section

/-! Integral-basis transport carries the actual rational integral
vacuum to the actual product of number-field integral vacua. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem local_coset_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest F N 1 one_ne_zero 0 v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  apply RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest_eq_vacuum
  · simpa only [map_one] using (v.adicCompletionIntegers F).one_mem
  · simpa only [inv_one, map_one] using (v.adicCompletionIntegers F).one_mem
  · intro i
    exact (v.adicCompletionIntegers F).zero_mem

theorem tensor_one : CMExtraction.Finite.TestTransport.finiteCosetTensor F N 1 one_ne_zero 0 =
    RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (Filter.Eventually.of_forall fun _ => rfl) := by
  have he : RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest F N 1 one_ne_zero 0 = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N := funext (local_coset_one F N)
  apply Subtype.ext
  exact congrArg (PiTensorProduct.tprod ℂ) he

theorem equivalence_lattice (q : ℚ) (hq : q ≠ 0) :
    Finite.AdelicTestCoordinates.CM.equivalence F N (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) =
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (CMExtraction.Finite.TestTransport.finiteCosetTensor F N (algebraMap ℚ F q)
        ((map_ne_zero (algebraMap ℚ F)).mpr hq) 0) := by
  apply Subtype.ext
  apply RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.denseRange_finiteRationalPosition.equalizer
    (Finite.AdelicTestCoordinates.CM.equivalence F N (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).property.1.continuous
    (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N _).1.continuous
  funext x
  change (Finite.AdelicTestCoordinates.CM.equivalence F N (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N _ (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)
  rw [Finite.AdelicTestCoordinates.CM.rational_value, CMExtraction.Finite.TestTransport.finiteCosetTensor_value]
  have h := Finite.TensorRepresentatives.CM.rational_coset_value F N q hq 0 x
  have hz : RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (0 : Fin N → F) = 0 := by
    funext i
    exact map_zero (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))
  change RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) x) = _
  simpa only [map_zero, hz, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator, sub_zero] using h

theorem equivalence_vacuum : Finite.AdelicTestCoordinates.CM.equivalence F N RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction =
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N
      (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (Filter.Eventually.of_forall fun _ => rfl)) := by
  have h := equivalence_lattice F N 1 one_ne_zero
  have hv : (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction 1 one_ne_zero : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Finite.AdelicTestCoordinates.CM.Index F N)) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction :=
    Subtype.ext Finite.IntegralVacuum.CM.latticeIndicator_one
  simpa only [hv, map_one, tensor_one] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralCoordinateVacuum.CM
