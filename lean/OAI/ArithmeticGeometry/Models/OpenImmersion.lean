import OAI.ArithmeticGeometry.Models.Open

/-! # Open Immersion -/

namespace OAI.ArithmeticGeometry.Models.OpenImmersion.Constructions.Foundations

/-! A compact open immersion can be modeled as an actual open immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

variable {K : Type u} [Field K]

theorem open_subset_in_ambient_model
    {X : Over (Spec (CommRingCat.of K))} (M : Foundations.Constructions.CoefficientModel K X)
    (U : X.left.Opens) (hU : IsCompact (U : Set X.left)) :
    ∃ (M' : Foundations.Constructions.CoefficientModel K X) (V : M'.model.left.Opens),
      IsCompact (V : Set M'.model.left) ∧ M'.specialization ⁻¹ᵁ V = U := by
  let e := M.expansionGenericIso
  have hU' : IsCompact (e.inv ⁻¹ᵁ U : Set (Descent.Constructions.Foundations.expansionCone (𝓞 K) K M.coefficients M.model).pt) :=
    e.inv.isCompact_preimage hU
  obtain ⟨i, V, hV, hi⟩ := Descent.Constructions.Foundations.compact_open_descends (𝓞 K) K M.coefficients M.model
    (e.inv ⁻¹ᵁ U) hU'
  refine ⟨M.atExpansion i, V, hV, ?_⟩
  rw [Foundations.Constructions.CoefficientModel.atExpansion_specialization]
  change (e.hom ≫ (Descent.Constructions.Foundations.expansionCone (𝓞 K) K M.coefficients M.model).π.app i) ⁻¹ᵁ V = U
  rw [Scheme.Hom.comp_preimage, hi, ← Scheme.Hom.comp_preimage, e.hom_inv_id]
  rfl

structure OpenImmersionModel
    {W X : Over (Spec (CommRingCat.of K))} (f : W ⟶ X) where
  ambient : Foundations.Constructions.CoefficientModel K X
  source : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K ambient.coefficients)
  sourceFP : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism source.hom
  inclusion : source ⟶ ambient.model
  openInclusion : IsOpenImmersion inclusion.left
  specialization : W.left ⟶ source.left
  cartesian : IsPullback specialization W.hom source.hom
    (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K ambient.coefficients)
  compatibility : f.left ≫ ambient.specialization = specialization ≫ inclusion.left

theorem open_immersion_has_model
    {W X : Over (Spec (CommRingCat.of K))} (f : W ⟶ X)
    [IsOpenImmersion f.left] [CompactSpace W.left] (M : Foundations.Constructions.CoefficientModel K X) :
    Nonempty (OpenImmersionModel f) := by
  have hU : IsCompact (f.left.opensRange : Set X.left) :=
    isCompact_range f.left.continuous
  obtain ⟨M', V, hV, hpre⟩ := open_subset_in_ambient_model M f.left.opensRange hU
  let : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  let : LocallyOfFinitePresentation M'.model.hom := M'.finitePresentation.1
  let : QuasiSeparated M'.model.hom := M'.finitePresentation.2.2
  let : QuasiSeparatedSpace M'.model.left := quasiSeparatedSpace_of_quasiSeparated M'.model.hom
  let : QuasiSeparatedSpace V.toScheme := quasiSeparatedSpace_of_quasiSeparated V.ι
  have hfp : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (V.ι ≫ M'.model.hom) :=
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
      (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K M'.coefficients) := by
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

end OAI.ArithmeticGeometry.Models.OpenImmersion.Constructions.Foundations
