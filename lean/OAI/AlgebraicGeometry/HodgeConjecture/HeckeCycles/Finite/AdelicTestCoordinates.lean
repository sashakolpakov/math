import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralAdelicCoordinates
import OAI.RepresentationTheory.Theta.Adelic.CompactSupport
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Adelic Test Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

noncomputable section

/-! Actual finite Schwartz functions in integral-basis coordinates over
a number field and over the rational finite adeles. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralAdelicCoordinates.TestTransport OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

abbrev Index := Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F)

def toField (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Index F N)) : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N :=
  ⟨φ.val ∘ CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N),
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp φ.property).1.comp_continuous
      (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N)).continuous,
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport φ).comp_homeomorph _⟩

def toRational (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Index F N) :=
  ⟨φ.val ∘ (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N)).symm,
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
      ⟨φ.property.1.comp_continuous (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N)).symm.continuous,
        φ.property.2.comp_homeomorph _⟩⟩

def equivalence : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Index F N) ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N where
  toFun := toField F N
  invFun := toRational F N
  left_inv φ := by
    apply Subtype.ext
    funext x
    exact congrArg φ.val ((CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N)).apply_symm_apply x)
  right_inv φ := by
    apply Subtype.ext
    funext x
    exact congrArg φ.val ((CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N)).symm_apply_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rational_value (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Index F N)) (x : Fin N → F) :
    (equivalence F N φ).val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) x)) :=
  congrArg φ.val (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph_rational F (Fin N) x)

theorem inverse_rational_value (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) (x : Fin N → F) :
    ((equivalence F N).symm φ).val
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) x)) =
      φ.val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
  change φ.val ((CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F (Fin N)).symm
    (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralCoordinateDiagonal F (Fin N) x)) = _
  rw [← CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph_rational, Homeomorph.symm_apply_apply]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM
