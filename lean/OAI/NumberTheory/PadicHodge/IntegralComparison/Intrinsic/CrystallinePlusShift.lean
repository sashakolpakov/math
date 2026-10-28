import OAI.NumberTheory.PadicHodge.CrystallineGroupLaw

/-! # Crystalline Plus Shift -/

namespace OAI.NumberTheory.PadicHodge

noncomputable section

/-! The actual crystalline pullback of [n]+F is the sum of the scalar
operator and the original crystalline Frobenius. The group-law identity
is supplied by the proved geometry of the original model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

include j P

theorem GeometricComparison.Geometry.AbelianH1Model.crystallinePullback_plus_nat (n : ℕ) :
    GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q
      (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
        AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom) =
      algebraMap ℚ_[q] (Module.End ℚ_[q] A.Crystalline) (n : ℚ_[q]) + A.crystallineFrobenius := by
  change CrystallineGroupLaw.FrobeniusSlope.crystallineRingAction q A j P
    (MulOpposite.op ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme)) = _
  rw [MulOpposite.op_add, map_add, MulOpposite.op_natCast, map_natCast, map_natCast]
  rfl

end

end OAI.NumberTheory.PadicHodge
