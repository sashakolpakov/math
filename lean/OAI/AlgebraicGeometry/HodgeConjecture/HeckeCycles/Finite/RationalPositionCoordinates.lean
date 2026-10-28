import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.MatrixExtension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TensorRepresentatives

/-! # Rational Position Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.RationalPositionCoordinates.CM

noncomputable section

/-! Any actual rational position frame extends to finite adeles and
transports the actual finite Schwartz functions and tensor representatives. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  {I : Type} [Fintype I] [DecidableEq I] (r : (Fin N → F) ≃ₗ[ℚ] (I → ℚ))

def changeOfBasis : (AdelicTestCoordinates.CM.Index F N → ℚ) ≃ₗ[ℚ] (I → ℚ) :=
  (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N)).symm.trans r

def homeomorphism : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N)).trans
    (Rational.MatrixExtension.CM.continuousEquivalence RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (changeOfBasis F N r)).toHomeomorph

theorem rational (x : Fin N → F) :
    homeomorphism F N r (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (r x) := by
  change Rational.MatrixExtension.CM.continuousEquivalence RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (changeOfBasis F N r)
    (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) = _
  have hi : CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) x) :=
    CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph_rational F (Fin N) x
  rw [hi]
  refine (Rational.MatrixExtension.CM.continuous_rational RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (changeOfBasis F N r)
    (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) x)).trans ?_
  funext i
  exact congrArg (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (congrFun (congrArg r
    ((CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N)).symm_apply_apply x)) i)

def toField (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N :=
  ⟨φ.val ∘ homeomorphism F N r,
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp φ.property).1.comp_continuous (homeomorphism F N r).continuous,
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport φ).comp_homeomorph _⟩

def toRational (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  ⟨φ.val ∘ (homeomorphism F N r).symm,
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
      ⟨φ.property.1.comp_continuous (homeomorphism F N r).symm.continuous,
        φ.property.2.comp_homeomorph _⟩⟩

def equivalence : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N where
  toFun := toField F N r
  invFun := toRational F N r
  left_inv φ := by
    apply Subtype.ext
    funext x
    exact congrArg φ.val ((homeomorphism F N r).apply_symm_apply x)
  right_inv φ := by
    apply Subtype.ext
    funext x
    exact congrArg φ.val ((homeomorphism F N r).symm_apply_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rational_value (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : Fin N → F) :
    (equivalence F N r φ).val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) = φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (r x)) :=
  congrArg φ.val (rational F N r x)

theorem inverse_rational_value (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) (x : Fin N → F) :
    ((equivalence F N r).symm φ).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (r x)) = φ.val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
  change φ.val ((homeomorphism F N r).symm (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (r x))) = _
  rw [← rational, Homeomorph.symm_apply_apply]

def tensorSection : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N :=
  (TensorRepresentatives.CM.sectionMap F N).comp (equivalence F N r).toLinearMap

theorem tensor_value (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (tensorSection F N r φ) x =
      φ.val (homeomorphism F N r x) :=
  TensorRepresentatives.CM.section_value F N (equivalence F N r φ) x

theorem tensor_rational (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : Fin N → F) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (tensorSection F N r φ) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (r x)) := by
  rw [tensor_value, rational]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.RationalPositionCoordinates.CM
