import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base
import Mathlib.RingTheory.Etale.Field

/-! # Field Extension Reduced -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The finite number-field extension in an arithmetic base is finite
etale. Its base change preserves the actual reduction of a reference model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ)

theorem Base.ArithmeticBaseExtension.fieldExtension_finite_etale : IsFinite B.fieldExtension ∧ Etale B.fieldExtension := by
  have : Algebra.FormallyEtale K B.extension.carrier :=
    Algebra.FormallyEtale.of_isSeparable K B.extension.carrier
  have : Algebra.Etale K B.extension.carrier :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  constructor
  · apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap K B.extension.carrier))).mpr
    exact (RingHom.finite_algebraMap).mpr inferInstance
  · apply (HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap K B.extension.carrier))).mpr
    exact (RingHom.etale_algebraMap).mpr inferInstance

theorem Base.ArithmeticBaseExtension.fieldExtension_isReduced (X : Over (Spec (.of K))) [IsReduced X.left] :
    IsReduced ((Over.pullback B.fieldExtension).obj X).left := by
  have := (Base.ArithmeticBaseExtension.fieldExtension_finite_etale B).1
  have := (Base.ArithmeticBaseExtension.fieldExtension_finite_etale B).2
  exact Finite.EtaleReduced.finite_etale_isReduced (CategoryTheory.Limits.pullback.fst X.hom B.fieldExtension)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
