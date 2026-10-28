import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonBetti
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralFinite
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SummandTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Comparison

noncomputable section

/-! One full GeometricComparison realization carries all native minuscule and central
operators. Restriction to the active algebra preserves its actual
endomorphism presentations and every cohomological action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

section

variable {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {jq : K →+* ℚ_[q]} (B : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  {H J : Type} [CommRing H] [Algebra ℚ H] [CommRing J] [Algebra ℚ J]

def restrictHeckeRealization (R : B.HeckeRealization H) (f : J →ₐ[ℚ] H) : B.HeckeRealization J where
  action := R.action.comp f
  presentation j := R.presentation (f j)
  represents j := R.represents (f j)

theorem restrictHeckeRealization_betti (R : B.HeckeRealization H) (f : J →ₐ[ℚ] H)
    (j : K →+* ℂ) (h : J) :
    B.bettiHecke j (restrictHeckeRealization B R f) h = B.bettiHecke j R (f h) := rfl

theorem restrictHeckeRealization_complex (R : B.HeckeRealization H) (f : J →ₐ[ℚ] H)
    (j : K →+* ℂ) (h : J) :
    B.complexBettiHecke j (restrictHeckeRealization B R f) h = B.complexBettiHecke j R (f h) := rfl

theorem restrictHeckeRealization_deRham (R : B.HeckeRealization H) (f : J →ₐ[ℚ] H) (h : J) :
    B.deRhamHecke (restrictHeckeRealization B R f) h = B.deRhamHecke R (f h) := rfl

end

namespace Intrinsic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Comparison
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement.Spectral

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

abbrev nativeFullCommRing (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
  { (inferInstance : Ring (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with mul_comm := AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors }

theorem native_full_comparison_realization
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hq hIsogenyQuotient) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    letI := nativeFullCommRing (s := s) hElementaryDivisors
    ∃ R : (Intrinsic.Comparison.nativeComparisonModel D hg hq j).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q),
      R.action = (HeckeCycles.EndomorphismComparison.CM.rationalEquiv (Intrinsic.Comparison.nativeComparisonModel D hg hq j).variety.scheme).toAlgHom.comp
        A.algebraAction ∧
      (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding R = (fun h => (A.cohomologyAction h : Module.End ℚ D.pel.H1)) := by
  let := nativeFullCommRing (s := s) hElementaryDivisors
  exact HeckeCycles.Intrinsic.ComparisonAction.CM.native_hecke_realization D.pel hg j hq.2.2.2.1
    A.algebraAction A.cohomologyAction hA.cohomology

theorem native_full_comparison_intertwining
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    letI := nativeFullCommRing (s := s) hElementaryDivisors
    ∀ (R : (Intrinsic.Comparison.nativeComparisonModel D hg hq j).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)),
      (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding R = (fun h => (A.cohomologyAction h : Module.End ℚ D.pel.H1)) →
      ∀ h x, ComparisonBetti.Intrinsic.nativeBettiComplexification D hg ((A.cohomologyAction h).baseChange ℂ x) =
        (Intrinsic.Comparison.nativeComparisonModel D hg hq j).complexBettiHecke D.pel.complexEmbedding R h
          (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg x) := by
  let := nativeFullCommRing (s := s) hElementaryDivisors
  intro R hR h x
  have hc := ComparisonBetti.coefficientExtension_hecke (Intrinsic.Comparison.nativeComparisonModel D hg hq j)
    D.pel.complexEmbedding R h x
  rw [congrFun hR h] at hc
  exact hc

theorem native_full_comparison_restrict_active
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    letI := nativeFullCommRing (s := s) hElementaryDivisors
    letI := Intrinsic.Comparison.nativeActiveCommRing D e hElementaryDivisors
    ∀ (R : (Intrinsic.Comparison.nativeComparisonModel D hg hq j).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)),
      (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding R = (fun h => (A.cohomologyAction h : Module.End ℚ D.pel.H1)) →
      (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding
        (restrictHeckeRealization (Intrinsic.Comparison.nativeComparisonModel D hg hq j) R
          (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e)) =
        (fun h => (Intrinsic.Forms.activeBettiAction D A e h : Module.End ℚ D.pel.H1)) := by
  let := nativeFullCommRing (s := s) hElementaryDivisors
  let := Intrinsic.Comparison.nativeActiveCommRing D e hElementaryDivisors
  intro R hR
  funext h
  exact congrFun hR (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e h)

theorem native_full_comparison_summand
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    letI := nativeFullCommRing (s := s) hElementaryDivisors
    ∀ (R : (Intrinsic.Comparison.nativeComparisonModel D hg hq j).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)),
      (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding R =
        (fun h => (A.cohomologyAction h : Module.End ℚ D.pel.H1)) →
      ∀ χ : ℂ ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ,
        (HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D.pel ℂ A) χ).map
          (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg).toLinearMap =
        (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHeckeSummand D.pel.complexEmbedding R
          (fun h => χ (1 ⊗ₜ[ℚ] h)) := by
  let := nativeFullCommRing (s := s) hElementaryDivisors
  intro R hR χ
  rw [CharacterRefinement.Spectral.jointSpace_scalar_extension]
  simp only [Intrinsic.CentralFinite.nativeFullHeckeActionOver_tmul, one_smul]
  exact SummandTransport.Comparison.jointSpace_map_equiv (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg) _ _
    (native_full_comparison_intertwining D hg hq A hElementaryDivisors j R hR) (fun h => χ (1 ⊗ₜ[ℚ] h))

end Intrinsic

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Comparison
