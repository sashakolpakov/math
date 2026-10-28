import OAI.NumberTheory.PadicHodge.IntrinsicParameters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison

/-! # Intrinsic Model -/

namespace OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic

noncomputable section

/-! Construct the GeometricComparison realization on TateComparison's exact Albanese and identify
the algebraic lift of the native occurring character with its Betti summand. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM.Summands OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

@[instance_reducible] def heckeCommRing (s q : ℕ) [Fact q.Prime] : CommRing (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
  { (inferInstance : Ring (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with
    mul_comm := AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q (RepresentationTheory.Hecke.SphericalActionModelInverse.cartanInput q) }

attribute [local instance] heckeCommRing

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
  (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)

abbrev model := AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hq.2.2.2.1

def realization : (model D hg hq j).HeckeRealization (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
  (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction.CM.native_hecke_realization D hg j hq.2.2.2.1 A.rho A.rhoH1 hTateComparison.cohomology).choose

theorem realization_betti :
    (model D hg hq j).bettiHecke D.complexEmbedding (realization D hg hq hIsogenyQuotient A hTateComparison j) =
      (fun h => A.rhoH1 h) :=
  (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction.CM.native_hecke_realization D hg j hq.2.2.2.1 A.rho A.rhoH1 hTateComparison.cohomology).choose_spec.2

theorem rational_character_occurs
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥) :
    AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.rationalAction D A h).baseChange ℂ)
      (fun h => χ (1 ⊗ₜ[ℚ] h)) ≠ ⊥ := by
  intro hz
  apply hχ
  apply eq_bot_iff.mpr
  apply le_trans ?_ hz.le
  intro x hx
  simp only [Submodule.mem_iInf] at hx
  simp only [AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace, Submodule.mem_iInf]
  intro h
  simpa only [RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction_tmul, one_smul] using hx (1 ⊗ₜ[ℚ] h)

theorem native_character_occurs
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥) :
    (model D hg hq j).bettiHeckeSummand (j.complexClosure.comp j.fieldInClosure)
      (realization D hg hq hIsogenyQuotient A hTateComparison j)
      (fun h => j.complexClosure (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ h)) ≠ ⊥ := by
  rw [j.complex_compatibility]
  let : FiniteDimensional ℚ ((model D hg hq j).Betti D.complexEmbedding) :=
    RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.rationalBetti_finite D hg
  rw [← AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM.Summands.betti_summand_identification]
  intro hz
  have hh := (Submodule.map_eq_bot_iff
    (e := AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM.coefficientEquiv (model D hg hq j) D.complexEmbedding)).mp hz
  rw [realization_betti] at hh
  simp only [IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter_image] at hh
  exact rational_character_occurs D A χ hχ hh

end

end OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic
