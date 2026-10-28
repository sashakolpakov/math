import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients

/-! # Quotient Equation Scalar Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.QuotientEquationScalarChange.Constructions

noncomputable section

/-! Quotienting by a base-ring equation agrees with quotienting by
its algebra image, with the original scalar action retained. -/

open scoped Pointwise

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (r : R)

theorem smul_top_restrict :
    r • (⊤ : Submodule R M) =
      ((algebraMap R S r) • (⊤ : Submodule S M)).restrictScalars R := by
  ext x
  change x ∈ r • (⊤ : Submodule R M) ↔ x ∈ (algebraMap R S r) • (⊤ : Submodule S M)
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, algebraMap_smul]

def quotientEquiv : QuotSMulTop r M ≃ₗ[R] QuotSMulTop (algebraMap R S r) M :=
  (Submodule.quotEquivOfEq _ _ (smul_top_restrict R S M r)).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

def algebraQuotientEquiv : QuotSMulTop r S ≃ₗ[R] S ⧸ Ideal.span {algebraMap R S r} :=
  (quotientEquiv R S S r).trans
    ((Submodule.quotEquivOfEq _ _
      (Regular.EquationQuotients.Constructions.smul_top_eq_span S (algebraMap R S r))).restrictScalars R)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.QuotientEquationScalarChange.Constructions
