import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Fin

/-! # Antilinear Dual Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AntilinearDualCoordinates

noncomputable section

/-! Evaluation on an actual complex basis embeds the antiholomorphic
dual into the corresponding coordinate space. -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (b : Module.Basis ι ℂ V)

def antilinearDualBasisCoordinates : (V →ₗ⋆[ℂ] ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun f i := f (b i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem antilinearDualBasisCoordinates_injective :
    Function.Injective (antilinearDualBasisCoordinates b) := by
  intro f g h
  exact b.ext (fun i => congrFun h i)

include b

theorem antilinearDual_finiteDimensional [Finite ι] :
    FiniteDimensional ℂ (V →ₗ⋆[ℂ] ℂ) :=
  FiniteDimensional.of_injective (antilinearDualBasisCoordinates b)
    (antilinearDualBasisCoordinates_injective b)

theorem antilinearDual_finrank_le [Fintype ι] :
    Module.finrank ℂ (V →ₗ⋆[ℂ] ℂ) ≤ Fintype.card ι := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective (antilinearDualBasisCoordinates_injective b)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AntilinearDualCoordinates
