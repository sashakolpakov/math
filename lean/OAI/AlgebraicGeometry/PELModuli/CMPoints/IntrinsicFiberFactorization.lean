import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarFactorTransport
import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianArithmeticModels

/-! # Intrinsic Fiber Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The native CM factorization acts on the literal universal-family
fiber, whose original number-field model is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

instance IntrinsicFiberFactorization.nativePolarizedAtIso_group {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    IsMonHom (IntrinsicFiber.nativePolarizedAtIso P p).hom :=
  AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso_isMonHom _ _

def IntrinsicFiberFactorization.abelianNumberFieldModelOfFiber
    {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (F : Subfield ℂ) [NumberField F] (p : Spec (.of F) ⟶ S) :
    AbelianArithmeticModels.AbelianNumberFieldModel (A.pullback (Spec.map (CommRingCat.ofHom F.subtype) ≫ p)) where
  field := F
  abelian := A.pullback p
  comparison := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.scheme p
    (Spec.map (CommRingCat.ofHom F.subtype)) (Spec.map (CommRingCat.ofHom F.subtype) ≫ p) rfl
  group := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _

theorem IntrinsicFiberFactorization.exists_coordinate_CM_fiber_factorization
    (hCMAbelianVariety : Descent.AbelianInput)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {hP : P.IsAdmissible}
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (Q : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (hCM : CoordinateRealization.HasCoordinateCMRealization P hP (IntrinsicFiber.nativePolarizedAt Q p)) :
    ∃ C : ∀ i : Fin 3, IntegralModel.CMIntegralModel (PeriodCoordinates.coordinateCMType P hP i),
      (∀ i, ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel (C i).realization.abelianVariety) ∧
      Nonempty (TorsionFactorIso.AbelianScalarFactorization (Q.abelian.pullback p) (fun i => (C i).abelianScheme)) := by
  obtain ⟨C, hC, ⟨D⟩⟩ := hCM.exists_integral_factorization hCMAbelianVariety
  refine ⟨C, hC, ⟨D.toAbelian (Q.abelian.pullback p) (fun i => (C i).abelianScheme)
    (IntrinsicFiber.nativePolarizedAtIso Q p) (fun _ => Iso.refl _) inferInstance ?_⟩⟩
  intro i
  exact inferInstanceAs (IsMonHom (𝟙 (C i).realization.abelianVariety.toOver))

theorem IntegralModel.CMIntegralModel.hasAbelianNumberFieldModel
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {Φ : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E} (C : IntegralModel.CMIntegralModel Φ)
    (hC : ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel C.realization.abelianVariety) :
    Nonempty (AbelianArithmeticModels.AbelianNumberFieldModel C.abelianScheme) := by
  let e : C.realization.abelianVariety.toOver ≅ C.abelianScheme.scheme := Iso.refl _
  let : IsMonHom e.hom := inferInstanceAs (IsMonHom (𝟙 C.realization.abelianVariety.toOver))
  exact AbelianArithmeticModels.exists_abelian_numberField_model C.abelianScheme C.realization.abelianVariety e hC

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
