import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenModels

/-! # Open Immersion Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionModels.Coefficients

/-! Generalization of the proved OpenImmersionModels construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 A compact open immersion can be modeled as an actual open immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

variable {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K]

theorem open_subset_in_ambient_model
    {X : Over (Spec (CommRingCat.of K))} (M : Models.Coefficients.CoefficientModel R₀ K X)
    (U : X.left.Opens) (hU : IsCompact (U : Set X.left)) :
    ∃ (M' : Models.Coefficients.CoefficientModel R₀ K X) (V : M'.model.left.Opens),
      IsCompact (V : Set M'.model.left) ∧ M'.specialization ⁻¹ᵁ V = U := by
  let e := M.expansionGenericIso
  have hU' : IsCompact (e.inv ⁻¹ᵁ U : Set (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R₀ K M.coefficients M.model).pt) :=
    e.inv.isCompact_preimage hU
  obtain ⟨i, V, hV, hi⟩ := ArithmeticGeometry.Models.Descent.Constructions.Foundations.compact_open_descends R₀ K M.coefficients M.model
    (e.inv ⁻¹ᵁ U) hU'
  refine ⟨M.atExpansion i, V, hV, ?_⟩
  rw [Models.Coefficients.CoefficientModel.atExpansion_specialization]
  change (e.hom ≫ (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R₀ K M.coefficients M.model).π.app i) ⁻¹ᵁ V = U
  rw [Scheme.Hom.comp_preimage, hi, ← Scheme.Hom.comp_preimage, e.hom_inv_id]
  rfl

structure OpenImmersionModel
    {W X : Over (Spec (CommRingCat.of K))} (f : W ⟶ X) where
  ambient : Models.Coefficients.CoefficientModel R₀ K X
  source : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K ambient.coefficients)
  sourceFP : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism source.hom
  inclusion : source ⟶ ambient.model
  openInclusion : IsOpenImmersion inclusion.left
  specialization : W.left ⟶ source.left
  cartesian : IsPullback specialization W.hom source.hom
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K ambient.coefficients)
  compatibility : f.left ≫ ambient.specialization = specialization ≫ inclusion.left

theorem open_immersion_has_model
    {W X : Over (Spec (CommRingCat.of K))} (f : W ⟶ X)
    [IsOpenImmersion f.left] [CompactSpace W.left] (M : Models.Coefficients.CoefficientModel R₀ K X) :
    Nonempty (OpenImmersionModel (R₀ := R₀) f) := by
  have hU : IsCompact (f.left.opensRange : Set X.left) :=
    isCompact_range f.left.continuous
  obtain ⟨M', V, hV, hpre⟩ := open_subset_in_ambient_model M f.left.opensRange hU
  let : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  let : LocallyOfFinitePresentation M'.model.hom := M'.finitePresentation.1
  let : QuasiSeparated M'.model.hom := M'.finitePresentation.2.2
  let : QuasiSeparatedSpace M'.model.left := quasiSeparatedSpace_of_quasiSeparated M'.model.hom
  let : QuasiSeparatedSpace V.toScheme := quasiSeparatedSpace_of_quasiSeparated V.ι
  have hfp : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (V.ι ≫ M'.model.hom) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hr : Set.range (f.left ≫ M'.specialization) ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    change M'.specialization (f.left w) ∈ V
    have hw : f.left w ∈ M'.specialization ⁻¹ᵁ V := by
      rw [hpre]
      exact ⟨w, rfl⟩
    exact hw
  let p := IsOpenImmersion.lift V.ι (f.left ≫ M'.specialization) hr
  have hp : p ≫ V.ι = f.left ≫ M'.specialization := IsOpenImmersion.lift_fac ..
  have hs : IsPullback p f.left V.ι M'.specialization :=
    IsOpenImmersion.isPullback _ _ _ _ hp.symm (by simpa using hpre)
  have hcart : IsPullback p W.hom (V.ι ≫ M'.model.hom)
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K M'.coefficients) := by
    rw [← f.w]
    exact hs.paste_vert M'.cartesian
  exact ⟨{
    ambient := M'
    source := Over.mk (V.ι ≫ M'.model.hom)
    sourceFP := hfp
    inclusion := Over.homMk V.ι rfl
    openInclusion := show IsOpenImmersion V.ι from inferInstance
    specialization := p
    cartesian := hcart
    compatibility := hp.symm }⟩

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionModels.Coefficients
