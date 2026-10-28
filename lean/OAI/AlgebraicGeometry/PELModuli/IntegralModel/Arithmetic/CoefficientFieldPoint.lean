import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Specialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CoefficientFiniteType

/-! # Coefficient Field Point -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A nonempty principal coefficient parameter admits an actual
point over a finite extension of the arithmetic generic field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

theorem Base.ArithmeticBaseExtension.coefficient_parameter_field_point (B : Base.ArithmeticBaseExtension K κ) [Algebra B.R ℂ]
    (hAlg : algebraMap B.R ℂ = B.embedding.comp B.toField)
    (s : Finset ℂ) (r : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s) (hr : r ≠ 0) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      D.denominator = N₀ ∧ ∃ j : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s →+* D.extension.carrier,
        j r ≠ 0 ∧ j.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s)) =
          (algebraMap B.extension.carrier D.extension.carrier).comp B.toField := by
  let S := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s
  let A := Localization.Away r
  have hrC : (r : ℂ) ≠ 0 := fun h => hr (Subtype.ext h)
  let c : A →+* ℂ := IsLocalization.Away.lift (g := algebraMap S ℂ) r (isUnit_iff_ne_zero.mpr hrC)
  have hc : c.comp (algebraMap B.R A) = B.embedding.comp B.toField := by
    ext x
    change c (algebraMap S A (algebraMap B.R S x)) = _
    rw [IsLocalization.Away.lift_eq]
    exact RingHom.congr_fun hAlg x
  have hft : Algebra.FiniteType B.R A := Algebra.FiniteType.trans (R := B.R) (S := S) (A := A)
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing_finiteType B.R ℂ s) inferInstance
  let Q : Over B.base := Over.mk (Spec.map (CommRingCat.ofHom (R := B.R) (S := A) (algebraMap B.R A)))
  have : LocallyOfFiniteType Q.hom := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr hft)
  let T := (Over.pullback B.generic).obj Q
  have : LocallyOfFiniteType T.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd Q.hom B.generic))
  have hw : Spec.map (CommRingCat.ofHom c) ≫ Q.hom =
      Spec.map (CommRingCat.ofHom B.embedding) ≫ B.generic := by
    change Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom (R := B.R) (S := A) (algebraMap B.R A)) =
      Spec.map (CommRingCat.ofHom B.embedding) ≫ Spec.map (CommRingCat.ofHom B.toField)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : B.R →+* ℂ => Spec.map (CommRingCat.ofHom f)) hc
  let w : Spec (.of ℂ) ⟶ T.left := pullback.lift (Spec.map (CommRingCat.ofHom c))
    (Spec.map (CommRingCat.ofHom B.embedding)) hw
  have : Nonempty T.left := ⟨w (IsLocalRing.closedPoint ℂ)⟩
  obtain ⟨D, p, hD⟩ := Arithmetic.Specialization.arithmetic_parameter_exists B.embedding T N₀ hN₀
  let a := p.left ≫ pullback.fst Q.hom B.generic
  let γ : A →+* D.extension.carrier := (Spec.preimage a).hom
  have hγ : Spec.map (CommRingCat.ofHom γ) = a := Spec.map_preimage a
  let j := γ.comp (algebraMap S A)
  have hjr : IsUnit (j r) := (IsLocalization.Away.algebraMap_isUnit (S := A) r).map γ
  refine ⟨D, hD, j, isUnit_iff_ne_zero.mp hjr, ?_⟩
  have ha : a ≫ Q.hom = D.fieldExtension ≫ B.generic := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun f => f ≫ B.generic) p.w
  have he : γ.comp (algebraMap B.R A) =
      (algebraMap B.extension.carrier D.extension.carrier).comp B.toField := by
    have heSpec : Spec.map (CommRingCat.ofHom (γ.comp (algebraMap B.R A))) =
        Spec.map (CommRingCat.ofHom ((algebraMap B.extension.carrier D.extension.carrier).comp B.toField)) := by
      change Spec.map (CommRingCat.ofHom (R := B.R) (S := A) (algebraMap B.R A) ≫ CommRingCat.ofHom γ) =
        Spec.map (CommRingCat.ofHom B.toField ≫
          CommRingCat.ofHom (algebraMap B.extension.carrier D.extension.carrier))
      rw [Spec.map_comp, Spec.map_comp, hγ]
      exact ha
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective heSpec)
  ext x
  exact RingHom.congr_fun he x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
