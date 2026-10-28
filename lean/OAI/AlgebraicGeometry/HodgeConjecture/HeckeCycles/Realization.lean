import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized

/-! # Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Realization.CM.RawHecke

noncomputable section

/-! Keep TateComparison's raw integral operators and geometric point formulas
alongside the very same GeometricComparison algebraic and Betti realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke

theorem action_on_integral_operator
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
    (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq) {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : H →ₐ[ℚ] AbelianScheme.TateComparison.End.RationalEnd A.variety.scheme) (R : A.HeckeRealization H)
    (hR : R.action = (EndomorphismComparison.CM.rationalEquiv A.variety.scheme).toAlgHom.comp ρ)
    (h : H) (f : AbelianScheme.TateComparison.End.IntegralEnd A.variety.scheme)
    (hf : AbelianScheme.TateComparison.End.endToRational A.variety.scheme f = ρ h) :
    R.action h = (1 : ℚ) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv A.variety.scheme f := by
  rw [hR]
  change EndomorphismComparison.CM.rationalEquiv A.variety.scheme (ρ h) = _
  rw [← hf, EndomorphismComparison.CM.rationalEquiv_integral]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop

theorem raw_realization_from_full_TateComparison
    (hTateComparison : TateComparison.CM.TateComparisonInput) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hgood : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    letI : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
    ∃ (basis : AbelianScheme.TateComparison.Local.LocalType s → AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (TAlb : AbelianScheme.TateComparison.Local.IntegralType s → D.EndK)
      (ρ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ) (T : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1)
      (R : (A).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)),
      (∀ t, AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t)) ∧
      (∀ t : AbelianScheme.TateComparison.Local.IntegralType s, D.toRational (TAlb t) = ρ (basis t.val)) ∧
      (∀ (t : AbelianScheme.TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (i : Fin D.componentCount)
          (x y : Over.mk b ⟶ D.componentGeneric i),
        D.endPoint (TAlb t) (D.aPoint hg i x - D.aPoint hg i y) =
          ((D.neighbors t b (x ≫ D.componentInclusion i)).map (D.aTotalPoint hg)).sum -
            ((D.neighbors t b (y ≫ D.componentInclusion i)).map (D.aTotalPoint hg)).sum) ∧
      (∀ h, D.IsRationalH1Pullback (ρ h) (T h)) ∧
      R.action = (EndomorphismComparison.CM.rationalEquiv (A).variety.scheme).toAlgHom.comp ρ ∧
      (A).bettiHecke D.complexEmbedding R = (fun h => T h) ∧
      (∀ t : AbelianScheme.TateComparison.Local.IntegralType s,
        R.action (basis t.val) = (1 : ℚ) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv (A).variety.scheme (TAlb t)) ∧
      (∀ (t : AbelianScheme.TateComparison.Local.IntegralType s) (ω : D.OneFormsA),
        AbelianScheme.TateComparison.Branches.IsBranchTrace (D.complexCorrespondence t) (D.albanesePullback hg ω)
          (D.albanesePullback hg (D.pullbackForms (TAlb t) ω))) := by
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
  obtain ⟨basis, TAlb, ρ, T, hbasis, hraw, hpoints, hH1, hforms⟩ :=
    TateComparisonAction.CM.actions_from_full_TateComparison hTateComparison s hs hdegree q D hg hgood hIsogenyQuotient hConstruction hElementaryDivisors
  obtain ⟨R, hR, hbetti⟩ := Intrinsic.ComparisonAction.CM.native_hecke_realization D hg j hcop ρ T hH1
  refine ⟨basis, TAlb, ρ, T, R, hbasis, hraw, hpoints, hH1, hR, hbetti, ?_, hforms⟩
  intro t
  exact action_on_integral_operator A ρ R hR (basis t.val) (TAlb t) (hraw t)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Realization.CM.RawHecke
