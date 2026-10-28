import OAI.AlgebraicGeometry.Resolution.Blowups.ResolutionGeometry
import Mathlib.Order.KrullDimension

/-! # Base Cases -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.BaseCases.Construction

noncomputable section

/-! The smooth and zero-dimensional base cases for Blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A smooth integral projective complex scheme is its own strong resolution. -/
theorem resolution_of_singularities_of_smooth
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X] [Smooth f]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) :
    letI : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
    ∃ (R : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : R.carrier ⟶ X),
      π ≫ f = R.structureMap ∧ IsProper π ∧
      (∃ e : R.carrier.PartialIso X, e.source.ι ≫ π = e.iso.hom ≫ e.target.ι) ∧
      IsIso (π ∣_ f.smoothLocus) := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  let R : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
    ⟨{ carrier := X, structureMap := f, projective := P, smooth := inferInstance }, inferInstance⟩
  refine ⟨R, 𝟙 X, Category.id_comp f, inferInstance, ?_, ?_⟩
  · refine ⟨Scheme.PartialIso.refl X, ?_⟩
    change (⊤ : X.Opens).ι ≫ 𝟙 X = 𝟙 (⊤ : X.Opens).toScheme ≫ (⊤ : X.Opens).ι
    simp only [Category.comp_id, Category.id_comp]
  · change IsIso (𝟙 X ∣_ f.smoothLocus)
    exact IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (inferInstance : IsIso (𝟙 X)) f.smoothLocus

/-- An integral complex scheme of finite presentation and Krull dimension zero
is smooth: its dense smooth locus contains its unique point. -/
theorem smooth_of_krullDimLE_zero
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X]
    [LocallyOfFinitePresentation f] [Order.KrullDimLE 0 X] : Smooth f := by
  let : PartialOrder X := specializationOrder X
  have hdim : Order.krullDim X = 0 := le_antisymm
    (by simpa using (Order.KrullDimLE.krullDim_le (n := 0) (α := X)))
    Order.krullDim_nonneg
  let : Subsingleton X := Order.krullDim_eq_zero_iff_of_orderTop.mp hdim
  obtain ⟨x, hx⟩ := f.dense_smoothLocus_of_perfectField.nonempty
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_le_iff.mp
  intro y _
  exact (Subsingleton.elim x y) ▸ hx

/-- Strong resolution for an integral projective complex scheme of dimension zero. -/
theorem resolution_of_singularities_dim_zero
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X] [Order.KrullDimLE 0 X]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) :
    letI : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
    ∃ (R : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : R.carrier ⟶ X),
      π ≫ f = R.structureMap ∧ IsProper π ∧
      (∃ e : R.carrier.PartialIso X, e.source.ι ≫ π = e.iso.hom ≫ e.target.ι) ∧
      IsIso (π ∣_ f.smoothLocus) := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  let : Smooth f := smooth_of_krullDimLE_zero X f
  exact resolution_of_singularities_of_smooth X f P

end

end OAI.AlgebraicGeometry.Resolution.Blowups.BaseCases.Construction
