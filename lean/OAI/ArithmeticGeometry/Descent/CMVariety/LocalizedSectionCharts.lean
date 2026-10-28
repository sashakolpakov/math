import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedFamily

/-! # Localized Section Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedSectionCharts.Abelian.RelativeCharts

noncomputable section

/-!
Assemble the localized smooth base map and its genuine section into actual
analytic product charts centered at that section. Both localization algebra
structures and the finite relative chart data are constructed explicitly.
-/

open scoped Classical

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]

@[instance_reducible]
def localizedBaseAlgebra (a : R) :
    Algebra (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
  (LocalizedFamily.Abelian.RelativeCharts.localizedBaseMap (A := A) a).toRingHom.toAlgebra

theorem localizedBaseScalarTower (a : R) :
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
      localizedBaseAlgebra (A := A) a
    IsScalarTower ℂ (Localization.Away a) (Localization.Away (algebraMap R A a)) := by
  let : Algebra (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
    localizedBaseAlgebra (A := A) a
  exact IsScalarTower.of_algebraMap_eq (fun c => (LocalizedFamily.Abelian.RelativeCharts.localizedBaseMap (A := A) a).commutes c |>.symm)

theorem localizedBaseAlgebra_smooth [Algebra.Smooth R A] (a : R) :
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
      localizedBaseAlgebra (A := A) a
    Algebra.Smooth (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
  (LocalizedFamily.Abelian.RelativeCharts.localizedBaseMap_smooth (A := A) a).toAlgebra

/-- A finite complex presentation with abstract index types, retaining
the actual polynomial data without expanding enumerations in analytic norms. -/
structure ComplexPresentation (B : Type) [CommRing B] [Algebra ℂ B] where
  VariableIndex : Type
  RelationIndex : Type
  [variablesFintype : Fintype VariableIndex]
  [relationsFintype : Fintype RelationIndex]
  presentation : Algebra.SubmersivePresentation ℂ B VariableIndex RelationIndex

attribute [instance] ComplexPresentation.variablesFintype ComplexPresentation.relationsFintype

/-- Localizing the total space along the base element gives a smooth
relative algebra with its actual section and constructed zero-section
product charts. There is no remaining section-analyticity input. -/
theorem exists_localized_section_charts
    {I Sigma : Type} [Fintype I] [Fintype Sigma]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    [Algebra.Smooth R A] (a : R) (σ : A →ₐ[ℂ] Localization.Away a)
    (hσ : σ.comp (IsScalarTower.toAlgHom ℂ R A) = Algebra.algHom ℂ R (Localization.Away a))
    (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away a)) :
    ∃ Q : ComplexPresentation (Localization.Away a),
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
      localizedBaseAlgebra (A := A) a
    let : IsScalarTower ℂ (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
      localizedBaseScalarTower (A := A) a
    ∃ D : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.RelativePresentationAt (R := Localization.Away a)
        (y.comp (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ)),
      Nonempty (RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts
        (E := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates D.presentation.map → ℂ)
        (F := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates Q.presentation.map → ℂ)
        (y.comp (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ)) (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ)) := by
  obtain ⟨Q⟩ : Nonempty (ComplexPresentation (Localization.Away a)) := ⟨{
    VariableIndex := Unit ⊕ I
    RelationIndex := Unit ⊕ Sigma
    presentation := (Algebra.SubmersivePresentation.localizationAway (Localization.Away a) a).comp P }⟩
  refine ⟨Q, ?_⟩
  let : Algebra (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
    localizedBaseAlgebra (A := A) a
  let : IsScalarTower ℂ (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
    localizedBaseScalarTower (A := A) a
  let : Algebra.Smooth (Localization.Away a) (Localization.Away (algebraMap R A a)) :=
    localizedBaseAlgebra_smooth (A := A) a
  have hbase : IsScalarTower.toAlgHom ℂ (Localization.Away a)
      (Localization.Away (algebraMap R A a)) = LocalizedFamily.Abelian.RelativeCharts.localizedBaseMap (A := A) a := by
    ext r
    rfl
  have hret : (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ).comp
      (IsScalarTower.toAlgHom ℂ (Localization.Away a) (Localization.Away (algebraMap R A a))) =
        AlgHom.id ℂ (Localization.Away a) := by
    rw [hbase]
    exact LocalizedFamily.Abelian.RelativeCharts.localizedSection_retraction a σ hσ
  have hpoint : ((y.comp (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ)).comp
      (IsScalarTower.toAlgHom ℂ (Localization.Away a) (Localization.Away (algebraMap R A a)))).comp
        (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ) = y.comp (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ) := by
    rw [AlgHom.comp_assoc y, hret, AlgHom.comp_id]
  exact RegularSectionCharts.Abelian.RelativeCharts.exists_smooth_relative_section_charts Q.presentation
    (y.comp (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ)) (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hσ) hret hpoint

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedSectionCharts.Abelian.RelativeCharts
