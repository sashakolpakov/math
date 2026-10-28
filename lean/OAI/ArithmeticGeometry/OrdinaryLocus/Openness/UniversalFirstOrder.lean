import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.CharP.Algebra

/-! # Universal First Order -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UniversalFirstOrder.Construction

noncomputable section

/-! A universal first-order test ring for detecting zero differentials. -/

theorem isLocalRing_trivSqZeroExt
    (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsLocalRing (TrivSqZeroExt R M) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.fst_one] using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem charP_trivSqZeroExt
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (p : ℕ) [CharP R p] : CharP (TrivSqZeroExt R M) p := by
  exact charP_of_injective_ringHom (f := TrivSqZeroExt.inlHom R M)
    TrivSqZeroExt.inl_injective p

/-- A derivation gives the point whose infinitesimal coordinate is that derivation. -/
def derivationFirstOrderHom
    (k L M : Type*) [CommRing k] [CommRing L] [Algebra k L]
    [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M] [IsCentralScalar L M]
    [Module k M] [IsScalarTower k L M]
    (d : Derivation k L M) : L →ₐ[k] TrivSqZeroExt L M where
  toFun x := ⟨x, d x⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact d.map_add x y
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change d (x * y) = x • d y + MulOpposite.op y • d x
      rw [op_smul_eq_smul]
      exact d.leibniz x y
  commutes' r := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact d.map_algebraMap r

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UniversalFirstOrder.Construction
