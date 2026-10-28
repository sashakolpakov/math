import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.StalkIso
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

/-! # Iso Principal Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsoPrincipalDivisor

noncomputable section

/-! Native principal divisors transport exactly through scheme
isomorphisms, including all point coefficients and residue degrees. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

theorem pushforward {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsIso i] (hη : i (genericPoint X) = genericPoint Y) (g : Y.functionField) :
    CyclePushforward.pointPushforward i (Affine.DivisorNorm.rationalPrincipalDivisor X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη g)) =
      Affine.DivisorNorm.rationalPrincipalDivisor Y g := by
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη) :=
    inferInstanceAs (IsIso (Divisor.DivisorRestriction.openFieldMap i))
  ext y
  obtain ⟨x, rfl⟩ := i.surjective y
  rw [PushforwardFiber.pointPushforward_uniqueFiber i x (i x) rfl
      (fun z hz => i.isOpenEmbedding.injective hz),
    Principal.ClosedSectionCycle.residueDegree_immersion i x, Nat.cast_one, mul_one,
    Affine.DivisorNorm.rationalPrincipalDivisor_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply]
  exact congrArg (fun n : ℤ => (n : ℚ))
    (Divisor.StalkIso.ord_eq_of_stalkMap_isIso i hη x (coheight_eq_of_isOpenImmersion i) g)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsoPrincipalDivisor
