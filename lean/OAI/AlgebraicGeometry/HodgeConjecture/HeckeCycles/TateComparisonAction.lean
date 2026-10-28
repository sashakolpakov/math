import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Tate Comparison Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction.CM

noncomputable section

/-! Apply the complete named TateComparison input to the native geometric model.
The spherical algebra's commutativity is proved from ElementaryDivisors. The resulting
algebraic and Betti actions retain their raw operators and point formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison.CM

abbrev commutativeHeckeRing (s q : ℕ) [Fact q.Prime]
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
  { (inferInstance : Ring (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with
    mul_comm := AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors }

theorem actions_from_full_TateComparison
    (h_TateComparison : TateComparison.CM.TateComparisonInput)
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] (s : ℕ) (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) (q : ℕ) [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    ∃ (basis : AbelianScheme.TateComparison.Local.LocalType s → AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
      (TAlb : AbelianScheme.TateComparison.Local.IntegralType s → D.EndK)
      (ρ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ)
      (T : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1),
      (∀ t, AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t)) ∧
      (∀ t : AbelianScheme.TateComparison.Local.IntegralType s, D.toRational (TAlb t) = ρ (basis t.val)) ∧
      (∀ (t : AbelianScheme.TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (i : Fin D.componentCount)
          (x y : Over.mk b ⟶ D.componentGeneric i),
        D.endPoint (TAlb t) (D.aPoint hg i x - D.aPoint hg i y) =
          ((D.neighbors t b (x ≫ D.componentInclusion i)).map
            (D.aTotalPoint hg)).sum -
          ((D.neighbors t b (y ≫ D.componentInclusion i)).map
            (D.aTotalPoint hg)).sum) ∧
      (∀ h : AbelianScheme.TateComparison.HeckeKernel.Hecke s q, D.IsRationalH1Pullback (ρ h) (T h)) ∧
      (∀ (t : AbelianScheme.TateComparison.Local.IntegralType s) (ω : D.OneFormsA),
        AbelianScheme.TateComparison.Branches.IsBranchTrace (D.complexCorrespondence t) (D.albanesePullback hg ω)
          (D.albanesePullback hg (D.pullbackForms (TAlb t) ω))) := by
  obtain ⟨_hflags, basis, _coeff, _shift, hbasis, _hcoeff, _hconv, _hcentral,
    _hgraph, _hneighbors, _hclears, TAlb, ρ, T, hTAlb, hpoints, _hmul,
    _hunit, hH1, hforms⟩ := h_TateComparison s hs hdegree q D hg hgood hIsogenyQuotient hConstruction hElementaryDivisors
  exact ⟨basis, TAlb, ρ, T, hbasis, hTAlb, hpoints, hH1, hforms⟩

theorem native_hecke_operators_commute
    (s q : ℕ) [Fact q.Prime] (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    {V : Type} [AddCommGroup V] [Module ℚ V]
    (T : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ V) (h k : AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :
    Commute (T h) (T k) := by
  change T h * T k = T k * T h
  rw [← map_mul, AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors, map_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction.CM
