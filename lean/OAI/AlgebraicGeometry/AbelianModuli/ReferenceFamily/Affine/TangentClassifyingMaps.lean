import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.BaseTangentTests
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.BaseMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ComplexDualTests

/-! # Tangent Classifying Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual tangent tests on an affine chart of the native complex
moduli space give classifying maps over the original number field. On a
monic chart these maps detect the original derivation, including zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver
attribute [local implicit_reducible] Models.FinePELModel.complexFiber

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (κ : K →+* ℂ)
    (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ R ⟶ M.complexFiber κ)

def Models.FinePELModel.affineTangentClassifyingMap (d : Derivation ℂ R ℂ) : PEL.ComplexDualTests.pelComplexDualTest κ ⟶ M.space :=
  M.complexFamilyBaseMap κ (Affine.BaseTangentTests.affineBaseTangentTest ℂ R d ≫ f)

theorem Models.FinePELModel.affineTangentClassifyingMap_zero_constant (d : Derivation ℂ R ℂ) :
    M.affineTangentClassifyingMap κ R f 0 =
      PEL.ComplexDualTests.pelComplexDualProjection κ ≫ PEL.ComplexDualTests.pelComplexDualReduction κ ≫ M.affineTangentClassifyingMap κ R f d := by
  apply Over.OverMorphism.ext
  change (TangentBasePoint.tangentBasePoint ℂ R 0 ≫ f.left) ≫ pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom κ)) =
    Smooth.AffineDualProduct.dualBaseProjection ℂ ≫ Smooth.AffineDualProduct.dualBaseReduction ℂ ≫
      ((TangentBasePoint.tangentBasePoint ℂ R d ≫ f.left) ≫ pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom κ)))
  rw [TangentBasePoint.tangentBasePoint_zero_constant ℂ R d]
  simp only [Category.assoc]

theorem Models.FinePELModel.affineTangentClassifyingMap_injective [Mono f] :
    Function.Injective (M.affineTangentClassifyingMap κ R f) := by
  intro d e h
  have he := M.complexFamilyBaseMap_injective κ (EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ)) h
  exact Affine.BaseTangentTests.affineBaseTangentTest_injective ℂ R ((cancel_mono f).mp he)

theorem Models.FinePELModel.affineTangentClassifyingMap_constant_iff [Mono f] (d : Derivation ℂ R ℂ) :
    M.affineTangentClassifyingMap κ R f d =
      PEL.ComplexDualTests.pelComplexDualProjection κ ≫ PEL.ComplexDualTests.pelComplexDualReduction κ ≫ M.affineTangentClassifyingMap κ R f d ↔ d = 0 := by
  rw [← M.affineTangentClassifyingMap_zero_constant κ R f d]
  exact ⟨fun h => M.affineTangentClassifyingMap_injective κ R f h,
    fun h => congrArg (M.affineTangentClassifyingMap κ R f) h⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
