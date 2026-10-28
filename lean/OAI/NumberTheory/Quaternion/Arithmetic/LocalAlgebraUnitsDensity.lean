import OAI.NumberTheory.Quaternion.Arithmetic.NoncommutativeLocalModel
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAlgebraApproximation
import OAI.NumberTheory.Quaternion.Arithmetic.LocalCompletion

/-! # Local Algebra Units Density -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalAlgebraUnitsDensity

noncomputable section

/-! Unconditional finite-place weak approximation for the units of
any finite-dimensional number-field algebra, in concrete local models. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]
  {ι : Type*} [Fintype ι] (v : ι → HeightOneSpectrum (𝓞 F))
  (D : Type*) [Ring D] [Algebra F D] [FiniteDimensional F D]

def localFiniteAlgebraUnitMap (i : ι) : Dˣ →* (NoncommutativeLocalModel.localFiniteAlgebra ((v i).adicCompletion F) F D)ˣ :=
  Units.map (NoncommutativeLocalModel.localFiniteAlgebraCoefficients ((v i).adicCompletion F) F D).toMonoidHom

def finiteCompletionUnitMap (i : ι) : Fˣ →* ((v i).adicCompletion F)ˣ :=
  Units.map (algebraMap F ((v i).adicCompletion F)).toMonoidHom

theorem denseRange_localFiniteAlgebraCoefficients (hv : Function.Injective v) :
    DenseRange (fun a : D => fun i => NoncommutativeLocalModel.localFiniteAlgebraCoefficients ((v i).adicCompletion F) F D a) := by
  let b := Module.finBasis F D
  exact FiniteAlgebraApproximation.denseRange_finiteAlgebraDiagonal_of_bases v hv
    (fun i => NoncommutativeLocalModel.localFiniteAlgebraCoefficients ((v i).adicCompletion F) F D) b
    (fun i => NoncommutativeLocalModel.localFiniteAlgebraBasis ((v i).adicCompletion F) F D b)
    (fun i j => NoncommutativeLocalModel.localFiniteAlgebraBasis_apply ((v i).adicCompletion F) F D b j)

theorem denseRange_localFiniteAlgebraUnits (hv : Function.Injective v) :
    DenseRange (UnitsWeakApproximation.unitsPiDiagonal (fun i =>
      (NoncommutativeLocalModel.localFiniteAlgebraCoefficients ((v i).adicCompletion F) F D).toRingHom)) :=
  UnitsWeakApproximation.denseRange_unitsPiDiagonal (F := F) _
    (fun i => NoncommutativeLocalModel.localFiniteAlgebraCoefficients_injective ((v i).adicCompletion F) F D)
    (denseRange_localFiniteAlgebraCoefficients v D hv)

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalAlgebraUnitsDensity
