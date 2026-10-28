import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdicFiniteness
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! # Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.Finiteness

noncomputable section

/-! Finite first cohomology modulo ℓ implies finite generation of the
actual integral ℓ-adic H¹, by coefficient exactness and adic separation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection.Construction

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})

theorem hausdorff :
    IsHausdorff (Ideal.span {(ℓ : ℤ_[ℓ])}) (X.EllAdicCohomology ℓ 1) := by
  constructor
  intro x hx
  apply AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection.Construction.integralEllAdicH1_separated ℓ X x
  intro n
  exact (Principal.PowerModuleSequence.mem_submodule (ℤ_[ℓ])
    (X.EllAdicCohomology ℓ 1) (ℓ : ℤ_[ℓ]) n x).mp (SModEq.zero.mp (hx n))

theorem residue_finite [Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ 1 X).H 1)] :
    Finite ((X.EllAdicCohomology ℓ 1) ⧸
      ((Ideal.span {(ℓ : ℤ_[ℓ])}) • (⊤ : Submodule ℤ_[ℓ] (X.EllAdicCohomology ℓ 1)))) := by
  let M := X.EllAdicCohomology ℓ 1
  let P : Submodule ℤ_[ℓ] M := (Ideal.span {(ℓ : ℤ_[ℓ])}) • ⊤
  let f := AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ 1 X 1
  have hker : P.toAddSubgroup = f.ker := by
    ext x
    change x ∈ P ↔ f x = 0
    simpa only [P, f, Principal.PowerModuleSequence.submodule, pow_one] using
      (Principal.PowerModuleSequence.mem_submodule (ℤ_[ℓ]) M (ℓ : ℤ_[ℓ]) 1 x).trans
        (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction_one_eq_zero_iff ℓ 1 X x).symm
  change Finite (M ⧸ P.toAddSubgroup)
  rw [hker]
  exact Finite.of_injective (QuotientAddGroup.quotientKerEquivRange f)
    (QuotientAddGroup.quotientKerEquivRange f).injective

theorem finite_of_finite_reduction [Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ 1 X).H 1)] :
    Module.Finite ℤ_[ℓ] (X.EllAdicCohomology ℓ 1) := by
  let : IsAdicComplete (Ideal.span {(ℓ : ℤ_[ℓ])}) ℤ_[ℓ] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  let : IsHausdorff (Ideal.span {(ℓ : ℤ_[ℓ])}) (X.EllAdicCohomology ℓ 1) := hausdorff ℓ X
  let : Finite ((X.EllAdicCohomology ℓ 1) ⧸
      ((Ideal.span {(ℓ : ℤ_[ℓ])}) • (⊤ : Submodule ℤ_[ℓ] (X.EllAdicCohomology ℓ 1)))) :=
    residue_finite ℓ X
  exact Principal.AdicFiniteness.finite ℤ_[ℓ] (ℓ : ℤ_[ℓ]) (X.EllAdicCohomology ℓ 1)

theorem rational_finite_of_finite_reduction [Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ 1 X).H 1)] :
    FiniteDimensional ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] X.EllAdicCohomology ℓ 1) := by
  let : Module.Finite ℤ_[ℓ] (X.EllAdicCohomology ℓ 1) := finite_of_finite_reduction ℓ X
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.Finiteness
