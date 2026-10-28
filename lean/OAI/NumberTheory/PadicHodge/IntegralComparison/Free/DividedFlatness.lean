import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Basis
import Mathlib.RingTheory.RingHom.Flat

/-! # Divided Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedFlatness

noncomputable section

/-! Flatness of actual free divided-power extensions, over arbitrary coefficient rings. -/

universe u

variable (R σ : Type u) [CommRing R]

theorem free : Module.Free R (DividedPowerAlgebra R (σ →₀ R)) :=
  Module.Free.of_basis (AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Basis.FreeDividedBasis.basis R σ)

theorem flat : Module.Flat R (DividedPowerAlgebra R (σ →₀ R)) := by
  let : Module.Free R (DividedPowerAlgebra R (σ →₀ R)) := free R σ
  infer_instance

theorem algebraMap_flat : (algebraMap R (DividedPowerAlgebra R (σ →₀ R))).Flat :=
  RingHom.flat_algebraMap_iff.mpr (flat R σ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedFlatness
