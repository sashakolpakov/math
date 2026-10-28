import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticPointSpreading
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticBaseMaps

/-! # Arithmetic Field Point Spreading -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticFieldPointSpreading

noncomputable section

/-! Spread a point in a specified extension field on the original model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem field_point_on_fixed_arithmetic_model_spreads
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    {κ : K →+* ℂ} {κL : L →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (C : IntegralModel.Base.ArithmeticBaseExtension L κL)
    (i : B.extension.carrier →+* C.extension.carrier) (hdiv : B.denominator ∣ C.denominator)
    (X : Over B.base) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (x : Spec (.of C.extension.carrier) ⟶ X.left)
    (hx : x ≫ X.hom = Spec.map (CommRingCat.ofHom i) ≫ B.generic) :
    ∃ (D : ℕ) (hD : D ≠ 0) (hCD : C.denominator ∣ D),
      ∃ z : (C.withDenominator D hD).base ⟶ X.left,
        z ≫ X.hom = ArithmeticBaseMaps.arithmeticBaseMap B (C.withDenominator D hD) i (hdiv.trans hCD) ∧
        (C.withDenominator D hD).generic ≫ z = x := by
  let u := ArithmeticBaseMaps.arithmeticBaseMap B C i hdiv
  let Y := (Over.pullback u).obj X
  let y : Spec (.of C.extension.carrier) ⟶ Y.left :=
    pullback.lift x C.generic (hx.trans (ArithmeticBaseMaps.arithmeticBaseMap_generic B C i hdiv).symm)
  have hy : y ≫ Y.hom = C.generic := pullback.lift_snd _ _ _
  have hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom := by
    let : LocallyOfFinitePresentation X.hom := hX.1
    let : QuasiCompact X.hom := hX.2.1
    let : QuasiSeparated X.hom := hX.2.2
    change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback.snd X.hom u)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨D, hD, hCD, z, hz, hzg⟩ := ArithmeticPointSpreading.point_on_fixed_arithmetic_model_spreads C Y hY y hy
  refine ⟨D, hD, hCD, z ≫ pullback.fst X.hom u, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (z ≫ Y.hom) ≫ u = _
    rw [hz]
    exact ArithmeticBaseMaps.arithmeticBaseMap_enlarge B C i hdiv D hD hCD
  · rw [← Category.assoc, hzg]
    exact pullback.lift_fst _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticFieldPointSpreading
