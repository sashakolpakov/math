import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-! # Exterior Algebra Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorAlgebraBaseChange.ExteriorBaseChange

noncomputable section

/-! Exterior algebra scalar extension follows from the actual Clifford algebra comparison for the zero quadratic form. -/

open scoped TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [AddCommGroup M]
  [Algebra R S] [Module R M] [Invertible (2 : R)]

theorem zero_baseChange : (0 : QuadraticForm R M).baseChange S = 0 := by
  apply baseChange_ext
  intro m
  simp

def zeroIsometry : ((0 : QuadraticForm R M).baseChange S).IsometryEquiv
    (0 : QuadraticForm S (S ⊗[R] M)) where
  toLinearEquiv := LinearEquiv.refl S _
  map_app' x := by
    change 0 = (0 : QuadraticForm R M).baseChange S x
    rw [zero_baseChange]
    rfl

def algebraEquiv : S ⊗[R] ExteriorAlgebra R M ≃ₐ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  (CliffordAlgebra.equivBaseChange S (0 : QuadraticForm R M)).symm.trans
    (CliffordAlgebra.equivOfIsometry (zeroIsometry R S M))

theorem algebraEquiv_tmul_ι (s : S) (m : M) :
    algebraEquiv R S M (s ⊗ₜ[R] ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι S (s ⊗ₜ[R] m) := by
  change CliffordAlgebra.equivOfIsometry (zeroIsometry R S M)
    (CliffordAlgebra.ofBaseChange S (0 : QuadraticForm R M) (s ⊗ₜ[R] CliffordAlgebra.ι 0 m)) = _
  rw [CliffordAlgebra.ofBaseChange_tmul_ι]
  exact CliffordAlgebra.map_apply_ι _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorAlgebraBaseChange.ExteriorBaseChange
