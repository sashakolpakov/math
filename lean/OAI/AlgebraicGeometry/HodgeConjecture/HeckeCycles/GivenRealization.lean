import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Realization
import OAI.RepresentationTheory.Theta.Geometric.TateComparison

/-! # Given Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GivenRealization.CM.Hecke

noncomputable section

/-! Construct the comparison realization for a specified TateComparison action,
including the action returned by GeometricTheta. Its original integral operators
and Betti action are retained without selecting a second action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.RepresentationTheory.Theta.Geometric.TateComparison
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop

theorem realization (X : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hX : X.IsRealization D hg hq hIsogenyQuotient) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    letI : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
    ∃ R : (A).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q),
      R.action = (EndomorphismComparison.CM.rationalEquiv (A).variety.scheme).toAlgHom.comp X.algebraAction ∧
      (A).bettiHecke D.complexEmbedding R = (fun h => X.cohomologyAction h) ∧
      ∀ t : AbelianScheme.TateComparison.Local.IntegralType s,
        R.action (X.basis t.val) = (1 : ℚ) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv (A).variety.scheme (X.integral t) := by
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
  obtain ⟨R, hR, hbetti⟩ := Intrinsic.ComparisonAction.CM.native_hecke_realization
    D hg j hcop X.algebraAction X.cohomologyAction hX.cohomology
  exact ⟨R, hR, hbetti, fun t => Realization.CM.RawHecke.action_on_integral_operator
    A X.algebraAction R hR (X.basis t.val) (X.integral t) (hX.integral t)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GivenRealization.CM.Hecke
