import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison

/-! # Tower -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Collapse a constructed finite arithmetic tower, retaining the actual
complex embedding and native source pullback comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

def Base.ArithmeticBaseExtension.compose (B : Base.ArithmeticBaseExtension K κ)
    (C : Base.ArithmeticBaseExtension B.extension.carrier B.embedding) :
    Base.ArithmeticBaseExtension K κ := by
  let L := B.extension.carrier
  let M := C.extension.carrier
  let j : K →+* M := (algebraMap L M).comp (algebraMap K L)
  let : Algebra K M := j.toAlgebra
  have : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  exact {
    extension := ⟨M⟩
    embedding := C.embedding
    embedding_extends := by
      change C.embedding.comp ((algebraMap L M).comp (algebraMap K L)) = κ
      rw [← RingHom.comp_assoc, C.embedding_extends, B.embedding_extends]
    denominator := C.denominator
    denominator_ne_zero := C.denominator_ne_zero }

theorem Base.ArithmeticBaseExtension.compose_fieldExtension (B : Base.ArithmeticBaseExtension K κ)
    (C : Base.ArithmeticBaseExtension B.extension.carrier B.embedding) :
    C.fieldExtension ≫ B.fieldExtension = (B.compose C).fieldExtension := by
  change Spec.map (CommRingCat.ofHom (algebraMap B.extension.carrier C.extension.carrier)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K B.extension.carrier)) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap B.extension.carrier C.extension.carrier).comp (algebraMap K B.extension.carrier)))
  exact (Spec.map_comp _ _).symm

def Base.ArithmeticBaseExtension.composeSourceNatIso (B : Base.ArithmeticBaseExtension K κ)
    (C : Base.ArithmeticBaseExtension B.extension.carrier B.embedding) :
    Over.pullback B.fieldExtension ⋙ Over.pullback C.fieldExtension ≅
      Over.pullback (B.compose C).fieldExtension :=
  Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso B.fieldExtension C.fieldExtension
    (B.compose C).fieldExtension (Base.ArithmeticBaseExtension.compose_fieldExtension B C)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
