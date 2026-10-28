import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Rat.Encodable

/-! # Number Field Countability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NumberFieldCountability

noncomputable section

/-! The number-field bases in the original statement are countable. -/

theorem numberField_countable (K : Type) [Field K] [NumberField K] : Countable K :=
  Function.Injective.countable (Module.finBasis ℚ K).repr.injective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NumberFieldCountability
