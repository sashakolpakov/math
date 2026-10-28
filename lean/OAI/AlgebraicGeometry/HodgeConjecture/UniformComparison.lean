import OAI.AlgebraicGeometry.HodgeConjecture.ComparisonAssemblyUniformComparisonRadial
import OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicGeometricThetaComparison
import OAI.NumberTheory.PadicHodge.Occurrence

/-! # Uniform Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.UniformComparison.CMExtractionIntrinsic

noncomputable section

/-! Preserve the complete original geometric and radial output, and apply
comparison uniformly to its fixed radial parameters on the actual model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Matrix TensorProduct
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (u : MpF) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (v : CMExtraction.Multiplicity.Odd.Sign E)

def UniformFullOutput (hg : D.pel.HasIntegralModelGeometry)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (side : Fin s → Bool) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) : Prop :=
  Nonempty (NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D.pel hg hq j) ∧
  ∃ A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel,
    A.IsRealization D.pel hg hq hIsogenyQuotient ∧
  ∃ coeff : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s →
      AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ,
  ∃ hfull : AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hg hq hIsogenyQuotient (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff),
  ∃ (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (eComplex : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℂ]
      ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished),
    eComplex = RepresentationTheory.Theta.Geometric.Complexify.complexifyHeckeEquiv e ∧
    (∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight, ∃ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeSLRepresentative q a) T ∧
      RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e T = A.basis (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ∧
  ∃ (i : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex i) (cover : D.domain → X.analyticSpace),
    X.complexDimension = 2 ∧ D.IsPeriodUniformization X cover ∧
    (∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight,
      ∃ β : D.ClearedBranch (D.totalPeriodMap i X component cover) a ≃ RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeCosets q a,
        ∀ b : D.ClearedBranch (D.totalPeriodMap i X component cover) a,
          ∃ g : D.RationalSU,
            (QuotientGroup.mk (D.activeLocal g)⁻¹ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) = (β b).val ∧
            D.away g ∈ D.awayLevel ∧
            ∀ L : D.domain,
              D.clearedBranchTarget A.shift b L = D.totalPeriodMap i X component cover
                ⟨D.periodMap g L.val, D.periodMap_preserves g L.val L.property⟩) ∧
    (∀ h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      (D.activeH1Complex A e h).comp (D.ballH1ComplexProjector i) =
        (D.ballH1ComplexProjector i).comp (D.activeH1Complex A e h)) ∧
  ∃ rhoForms : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA,
    (∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rhoForms h)) ∧
  ∃ Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
    D.IsCanonicalThetaLift hg i (D.totalPeriodMap i X component cover) Θ ∧
    (∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg i (D.totalPeriodMap i X component cover) Ψ → Ψ = Θ) ∧
    (∀ (h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs),
      D.activeFormsComplex rhoForms e h (Θ φ) = Θ (D.sphericalWeilComplex h φ)) ∧
    (∀ f : D.sphericalInputs, Θ f ≠ 0 →
      ComparisonAssemblyUniformComparisonRadial.CMExtractionIntrinsic.UniformRadial E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms e Θ side j)

theorem uniformFullOutput_of_geometric
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (side : Fin s → Bool)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (hμ : D.pel.reference.μ = E.val.toRingHom) (hv : v.val 1 = true)
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel)
    (hpoly : CMExtraction.Intrinsic.OrdinaryPolynomial.NativeOrdinaryPolynomial D.pel hg hq hIsogenyQuotient side j)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (h : RepresentationTheory.Hecke.Geometric.GaloisValuation.GeometricGeometricThetaOutput E D u ιE v hg hq hIsogenyQuotient) :
    UniformFullOutput E D u ιE v hg hq hIsogenyQuotient side j := by
  let P := CMExtraction.Intrinsic.Albanese.nativeAlbaneseProjectiveOfGeometry D hg
  have hfull0 := NumberTheory.PadicHodge.Theta.FrobeniusSlope.fullOutput_of_geometric E D u ιE v
    hg P hq hIsogenyQuotient hTateComparison hμ hv hRationalStructure h
  have hfaith := NumberTheory.PadicHodge.Occurrence.FrobeniusSlope.faithfulOutput_of_original E D u ιE v
    hg P hq hIsogenyQuotient hfull0
  obtain ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, i, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := hfaith
  refine ⟨⟨CMExtraction.Intrinsic.ComparisonFiltration.nativeComparisonProjective D hg hq j⟩, A, hA, coeff, hfull,
    eH, eComplex, heComplex, hraw, i, X, component, cover, hdim, hcover,
    hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  refine ⟨hrad f hf, ?_⟩
  intro J ρ r M ω ζ happs
  have hside := CMExtraction.Intrinsic.CentralFinite.native_central_actions_finite_order D.pel hg hq hIsogenyQuotient hdegree
    hTateComparison A hA D.pel.reference.distinguished side
  exact ComparisonAssemblyUniformComparisonRadial.CMExtractionIntrinsic.uniform_comparison_of_faithful_applications E D ιE v hg hq hIsogenyQuotient
    A coeff hfull Θ side j hside hcomplex hopposite
    (hpoly (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull) hGeometricComparison J ρ r M ω ζ happs

theorem uniformFullOutput_to_original
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (side : Fin s → Bool)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (h : UniformFullOutput E D u ιE v hg hq hIsogenyQuotient side j) :
    NumberTheory.PadicHodge.Occurrence.FrobeniusSlope.FaithfulOutput E D u ιE v hg hq hIsogenyQuotient := by
  obtain ⟨_, A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, i, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := h
  exact ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, i, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov,
    fun f hf => (hrad f hf).1⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.UniformComparison.CMExtractionIntrinsic
