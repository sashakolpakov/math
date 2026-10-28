import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.TestTransport

/-! # Tensor Representatives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TensorRepresentatives.CM

noncomputable section

/-! Every actual finite adelic Schwartz function is represented by the
number-field restricted tensor construction. The proof expands the test
in genuine rational lattice cosets in integral-basis coordinates. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.TestTransport OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem rational_coset_value (q : ℚ) (hq : q ≠ 0) (a x : Fin N → F) :
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) a)
        (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) x) =
      RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator (algebraMap ℚ F q)
        ((map_ne_zero (algebraMap ℚ F)).mpr hq)
        (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
  have he : CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) x - CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) a ∈
        RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
      RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a ∈
        RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (algebraMap ℚ F q)
          ((map_ne_zero (algebraMap ℚ F)).mpr hq) := by
    rw [← map_sub]
    have hF : RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a =
        CMExtraction.IntegralAdelicCoordinates.TestTransport.fieldPositionDiagonal F (Fin N) (x - a) := (map_sub (CMExtraction.IntegralAdelicCoordinates.TestTransport.fieldPositionDiagonal F (Fin N)) x a).symm
    rw [hF]
    exact CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal_lattice_iff F (Fin N) q hq (x - a)
  simp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator, RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator,
    RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionIndicator, Set.indicator, SetLike.mem_coe, he]

theorem exists_rational_values (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (AdelicTestCoordinates.CM.Index F N)) :
    ∃ f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N,
      ∀ x : Fin N → F, RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        φ.val (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) x) := by
  obtain ⟨n, hn, s, hs⟩ := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.finiteSchwartz_coset_expansion_eq φ
  let q : ℚ := n
  have hq : q ≠ 0 := by change (n : ℚ) ≠ 0; exact_mod_cast hn.ne'
  let a := fun c => (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N)).symm (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c)
  let coeff := fun c => φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c))
  let T := fun c => CMExtraction.Finite.TestTransport.finiteCosetTensor F N (algebraMap ℚ F q)
    ((map_ne_zero (algebraMap ℚ F)).mpr hq) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c))
  have hT (c) (x : Fin N → F) :
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (T c) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c))).val
          (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) x) := by
    dsimp only [T]
    rw [CMExtraction.Finite.TestTransport.finiteCosetTensor_value, RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest_apply,
      ← rational_coset_value F N q hq (a c) x]
    simp only [CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal, a, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      LinearEquiv.apply_symm_apply]
  refine ⟨∑ c ∈ s, coeff c • T c, fun x => ?_⟩
  have hx := congrArg (fun ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (AdelicTestCoordinates.CM.Index F N) =>
    ψ.val (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) x)) hs
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, hT, smul_eq_mul]
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul] using hx.symm

theorem evaluation_surjective : Function.Surjective (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N) := by
  intro φ
  obtain ⟨f, hf⟩ := exists_rational_values F N ((AdelicTestCoordinates.CM.equivalence F N).symm φ)
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.denseRange_finiteRationalPosition.equalizer
    (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N f).1.continuous φ.property.1.continuous
  funext x
  exact (hf x).trans (AdelicTestCoordinates.CM.inverse_rational_value F N φ x)

theorem exists_linear_section :
    ∃ s : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N,
      (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N).comp s = LinearMap.id :=
  (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (evaluation_surjective F N))

def sectionMap :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N :=
  (exists_linear_section F N).choose

theorem section_value (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (sectionMap F N φ) x = φ.val x :=
  congrArg (fun ψ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N => ψ.val x)
    (LinearMap.congr_fun (exists_linear_section F N).choose_spec φ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TensorRepresentatives.CM
