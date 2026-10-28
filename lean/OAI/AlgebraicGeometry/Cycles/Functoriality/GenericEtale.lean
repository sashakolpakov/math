import OAI.AlgebraicGeometry.Cycles.Functoriality.GenericFiber
import OAI.AlgebraicGeometry.Cycles.Functoriality.EtaleLocus
import OAI.AlgebraicGeometry.Cycles.Functoriality.SupportFields
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratum

/-! # Generic Etale -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.GenericEtale.Construction

noncomputable section

section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S T : Scheme} [IsIntegral S] [IsIntegral T]

/-- Characteristic zero makes the finite generic extension separable,
so the actual stalk map is formally etale at the generic point. -/
theorem generic_stalk_formallyEtale (i : S ⟶ T) (g : T ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType i] [LocallyOfFiniteType g]
    (hη : i (genericPoint S) = genericPoint T)
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    (i.stalkMap (genericPoint S)).hom.FormallyEtale := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let : CharZero T.functionField := Algebra.charZero_of_charZero ℂ T.functionField
  let := (FunctionFields.Construction.genericFieldMap i hη).hom.toAlgebra
  let := FunctionFields.Construction.genericField_extension_finite i hη g hdim
  let : Algebra.IsSeparable T.functionField S.functionField := inferInstance
  have h : (FunctionFields.Construction.genericFieldMap i hη).hom.FormallyEtale :=
    Algebra.FormallyEtale.of_isSeparable T.functionField S.functionField
  exact (EtaleLocus.Construction.formallyEtale_respectsIso.cancel_left_isIso
    (T.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom
    (i.stalkMap (genericPoint S))).mp h

/-- A proper map that is formally etale at its unique point above the
target generic point is etale over a target Zariski-open neighborhood. -/
theorem exists_etale_target_neighborhood (i : S ⟶ T)
    [IsProper i] [LocallyOfFinitePresentation i]
    (hη : i (genericPoint S) = genericPoint T)
    (hfiber : i ⁻¹' {genericPoint T} = {genericPoint S})
    (het : (i.stalkMap (genericPoint S)).hom.FormallyEtale) :
    ∃ W : T.Opens, genericPoint T ∈ W ∧ Etale (i ∣_ W) := by
  obtain ⟨U, V, hVU, hηV, he⟩ := EtaleLocus.Construction.exists_etale_neighborhood i (genericPoint S) het
  let W : T.Opens := U ⊓
    ⟨(i '' (V : Set S)ᶜ)ᶜ, (i.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hηW : genericPoint T ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [← hη]
      exact hVU hηV
    · rintro ⟨x, hxV, hx⟩
      have hxη : x = genericPoint S := by
        have hxmem : x ∈ i ⁻¹' {genericPoint T} := hx
        rw [hfiber] at hxmem
        exact hxmem
      exact hxV (hxη ▸ hηV)
  have hpre : i ⁻¹ᵁ W ≤ V := by
    intro x hx
    by_contra hxV
    exact hx.2 ⟨x, hxV, rfl⟩
  refine ⟨W, hηW, ?_⟩
  let : Etale (i.resLE U V hVU) := he
  let : Etale (V.ι ≫ i) := by
    rw [← Scheme.Hom.resLE_comp_ι i hVU]
    infer_instance
  let : Etale ((i ⁻¹ᵁ W).ι ≫ i) := by
    rw [← S.homOfLE_ι hpre, Category.assoc]
    infer_instance
  let : Etale ((i ∣_ W) ≫ W.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  exact Etale.of_comp (i ∣_ W) W.ι

/-- A dimension-preserving proper morphism of integral complex varieties
is etale over a neighborhood of the target generic point. -/
theorem exists_generic_etale_open (i : S ⟶ T) (g : T ⟶ Spec (.of ℂ))
    [IsProper i] [LocallyOfFinitePresentation i] [LocallyOfFiniteType g]
    (hη : i (genericPoint S) = genericPoint T)
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    ∃ W : T.Opens, genericPoint T ∈ W ∧ Etale (i ∣_ W) :=
  exists_etale_target_neighborhood i hη (GenericFiber.Construction.genericFiber_eq_singleton i g hη hdim)
    (generic_stalk_formallyEtale i g hη hdim)

theorem etale_locallyQuasiFinite {A B : Scheme} (f : A ⟶ B) [Etale f] :
    LocallyQuasiFinite f where
  quasiFinite_appLE {U} hU {V} hV e := by
    let := (f.appLE U V e).hom.toAlgebra
    let : Algebra.Etale Γ(B, U) Γ(A, V) := f.etale_appLE hU hV e
    exact inferInstanceAs (Algebra.QuasiFinite Γ(B, U) Γ(A, V))

theorem exists_generic_finiteEtale_open (i : S ⟶ T) (g : T ⟶ Spec (.of ℂ))
    [IsProper i] [LocallyOfFinitePresentation i] [LocallyOfFiniteType g]
    (hη : i (genericPoint S) = genericPoint T)
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    ∃ W : T.Opens, genericPoint T ∈ W ∧ IsFinite (i ∣_ W) ∧ Etale (i ∣_ W) := by
  obtain ⟨W, hW, he⟩ := exists_generic_etale_open i g hη hdim
  let : Etale (i ∣_ W) := he
  let : LocallyQuasiFinite (i ∣_ W) := etale_locallyQuasiFinite _
  exact ⟨W, hW, IsFinite.of_isProper_of_locallyQuasiFinite _, he⟩

/-- The actual proper map of supports appearing in Functoriality is finite etale
over a Zariski-open neighborhood of the image support's generic point. -/
theorem supportImageMap_exists_finiteEtale_open
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    ∃ W : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (UnitCap.imageSupport f Z)).Opens,
      genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (UnitCap.imageSupport f Z)) ∈ W ∧
      IsFinite (SupportMap.Construction.supportImageMap f hf Z ∣_ W) ∧ Etale (SupportMap.Construction.supportImageMap f hf Z ∣_ W) := by
  let i := SupportMap.Construction.supportImageMap f hf Z
  let g := CycleClass.Geometric.SupportFiniteType.supportStructureMap (UnitCap.imageSupport f Z) Y.structureMap
  let : IsProper i := SupportMap.Construction.supportImageMap_isProper f hf Z
  let : IsProper g :=
    (Y.presentation.projective.reducedSupport (UnitCap.imageSupport f Z)).isProper
  let : IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme (UnitCap.imageSupport f Z)) :=
    Foundations.Scheme.ClosedProjective.isNoetherian_of_isProper_toSpec g
  apply exists_generic_finiteEtale_open i g (SupportMap.Construction.supportImageMap_genericPoint f hf Z)
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
    (SupportMap.Construction.supportImageMap f hf Z ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap (UnitCap.imageSupport f Z) Y.structureMap)
  rw [SupportMap.Construction.supportImageMap_over]
  exact hdim

end

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- The finite etale generic open can be chosen inside the target smooth
locus. Its entire inverse image is then smooth as well. -/
theorem exists_generic_smooth_finiteEtale_open
    {S T : Scheme} [IsIntegral S] [IsIntegral T]
    (i : S ⟶ T) (g : T ⟶ Spec (.of ℂ))
    [IsProper i] [LocallyOfFinitePresentation i] [LocallyOfFinitePresentation g]
    (hη : i (genericPoint S) = genericPoint T)
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    ∃ W : T.Opens, genericPoint T ∈ W ∧
      IsFinite (i ∣_ W) ∧ Etale (i ∣_ W) ∧
      Smooth (W.ι ≫ g) ∧ Smooth ((i ⁻¹ᵁ W).ι ≫ (i ≫ g)) := by
  obtain ⟨U, hU, hfin, het⟩ := exists_generic_finiteEtale_open i g hη hdim
  let : IsFinite (i ∣_ U) := hfin
  let : Etale (i ∣_ U) := het
  let W := U ⊓ g.smoothLocus
  have hW : U.ι ''ᵁ (U.ι ⁻¹ᵁ g.smoothLocus) = W := by
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, W]
  let e := morphismRestrictRestrict i U (U.ι ⁻¹ᵁ g.smoothLocus) ≪≫ morphismRestrictEq i hW
  let : MorphismProperty.RespectsIso (@IsFinite.{0} : MorphismProperty Scheme.{0}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro A B C e f hf
      let : IsFinite f := hf
      infer_instance
    · intro A B C e f hf
      let : IsFinite f := hf
      infer_instance
  let : MorphismProperty.RespectsIso (@Etale.{0} : MorphismProperty Scheme.{0}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro A B C e f hf
      let : Etale f := hf
      infer_instance
    · intro A B C e f hf
      let : Etale f := hf
      infer_instance
  let : IsFinite (i ∣_ W) := (MorphismProperty.arrow_mk_iso_iff
    (@IsFinite.{0} : MorphismProperty Scheme.{0}) e).mp inferInstance
  let : Etale (i ∣_ W) := (MorphismProperty.arrow_mk_iso_iff
    (@Etale.{0} : MorphismProperty Scheme.{0}) e).mp inferInstance
  let : Smooth (g.smoothLocus.ι ≫ g) := CycleClass.Geometric.SmoothStratum.smoothStratumToBase_isSmooth g
  have hle : W ≤ g.smoothLocus := inf_le_right
  let : Smooth (W.ι ≫ g) := by
    rw [← T.homOfLE_ι hle, Category.assoc]
    infer_instance
  refine ⟨W, ⟨hU, g.genericPoint_mem_smoothLocus_of_perfectField⟩,
    inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.GenericEtale.Construction
