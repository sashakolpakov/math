import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.CrystallinePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.FilteredLattice

/-! # Frobenius Divisibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.FrobeniusDivisibility.AbelianModel

noncomputable section

/-! The actual constructed integral crystalline Frobenius carries the
original native first Hodge lattice into its prime multiple. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.divisibility_integral_scheme_separated : A.integral.scheme.left.IsSeparated := ⟨by
  rw [← terminal.comp_from A.integral.scheme.hom]
  infer_instance⟩

local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.resolution (p := q)
  (J := Ideal.span {(q : WittVector q (ZMod q))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
  (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedIntegralFrobenius_eq_native : A.constructedIntegralFrobenius =
    IntrinsicPadic.IntegralFrobenius.IntrinsicPadicIntegralFrobenius.map q A.integral.scheme A.specialFiber.scheme
      A.integralReductionMorphism A.integralReductionSquare I A.specialFiber_projective := rfl

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedIntegralFrobenius_divisible
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1)
    (hx : x ∈ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 1) :
    ∃ y, A.constructedIntegralFrobenius x = (q : ℤ_[q]) • y := by
  rw [A.constructedIntegralFrobenius_eq_native]
  exact IntrinsicPadic.IntegralFrobenius.IntrinsicPadicIntegralFrobenius.divisible q A.integral.scheme A.specialFiber.scheme
    A.integralReductionMorphism A.integralReductionSquare I A.specialFiber_projective x hx

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedIntegralFrobenius_hodge_divisible
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1)
    (hx : A.integralDeRhamInclusion x ∈ A.Fil 1) :
    ∃ y, A.constructedIntegralFrobenius x = (q : ℤ_[q]) • y :=
  A.constructedIntegralFrobenius_divisible x ((A.integralDeRhamInclusion_mem_hodge_iff x).mp hx)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.FrobeniusDivisibility.AbelianModel
