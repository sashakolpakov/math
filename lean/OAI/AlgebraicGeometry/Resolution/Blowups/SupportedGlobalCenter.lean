import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Supported Global Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SupportedGlobalCenter.Construction

noncomputable section

/-! Extension of a closed center from an open subscheme when its entire
support lies in a closed stratum contained in that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The local closed center is closed in the whole scheme when the
support cannot leave a closed stratum contained in the chosen open. -/
theorem supported_center_composite_isClosedImmersion
    {C U X : Scheme.{u}} (i : C ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (Z : Set X) (hZ : IsClosed Z) (hCZ : Set.range (i ≫ j) ⊆ Z)
    (hZU : Z ⊆ Set.range j) : IsClosedImmersion (i ≫ j) := by
  apply IsClosedImmersion.of_isPreimmersion
  obtain ⟨D, hD, he⟩ := j.isOpenEmbedding.isInducing.image_eq_isClosed_inter_range
    i.isClosedEmbedding.isClosed_range
  have hcomp : j '' Set.range i = Set.range (i ≫ j) := (Set.range_comp j i).symm
  rw [hcomp] at he
  have hrange : Set.range (i ≫ j) = D ∩ Z := by
    ext x
    constructor
    · intro hx
      exact ⟨(he ▸ hx).1, hCZ hx⟩
    · rintro ⟨hxD, hxZ⟩
      exact he.symm ▸ ⟨hxD, hZU hxZ⟩
  rw [hrange]
  exact hD.inter hZ

/-- The kernel ideal sheaf of the extended center has exactly its actual
closed support; extension has introduced no additional closure points. -/
theorem supported_center_kernel_support
    {C U X : Scheme.{u}} (i : C ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (Z : Set X) (hZ : IsClosed Z) (hCZ : Set.range (i ≫ j) ⊆ Z)
    (hZU : Z ⊆ Set.range j) :
    ((i ≫ j).ker.support : Set X) = Set.range (i ≫ j) := by
  let : IsClosedImmersion (i ≫ j) := supported_center_composite_isClosedImmersion i j Z hZ hCZ hZU
  rw [Scheme.Hom.support_ker]
  exact (i ≫ j).isClosedEmbedding.isClosed_range.closure_eq

/-- Restricting the extended ideal sheaf to the original open recovers
the precise local center ideal sheaf. -/
theorem supported_center_kernel_comap
    {C U X : Scheme.{u}} (i : C ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (Z : Set X) (hZ : IsClosed Z) (hCZ : Set.range (i ≫ j) ⊆ Z)
    (hZU : Z ⊆ Set.range j) : (i ≫ j).ker.comap j = i.ker := by
  let : IsClosedImmersion (i ≫ j) := supported_center_composite_isClosedImmersion i j Z hZ hCZ hZU
  have hpb : IsPullback i (𝟙 C) j (i ≫ j) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  ext1
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (i ≫ j) i (𝟙 C) j hpb W).symm

/-- A center confined to a proper closed stratum has a nonzero global
ideal sheaf, as required by the integral global blowup construction. -/
theorem supported_center_kernel_ne_bot
    {C U X : Scheme.{u}} (i : C ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (Z : Set X) (hZ : IsClosed Z) (hCZ : Set.range (i ≫ j) ⊆ Z)
    (hZU : Z ⊆ Set.range j) (hproper : Z ≠ Set.univ) : (i ≫ j).ker ≠ ⊥ := by
  intro hzero
  have hs := supported_center_kernel_support i j Z hZ hCZ hZU
  rw [hzero] at hs
  have hrange : Set.range (i ≫ j) = Set.univ := hs.symm
  apply hproper
  apply Set.eq_univ_of_univ_subset
  rwa [← hrange]

/-- A local center supported in a proper closed stratum defines a genuine
global proper birational blowup. The whole complement of that stratum
is unchanged. No choice or termination of centers is asserted here. -/
theorem supported_global_center_blowup_step
    {C U X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (i : C ⟶ U) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (Z : Set X) (hZ : IsClosed Z) (hCZ : Set.range (i ≫ j) ⊆ Z)
    (hZU : Z ⊆ Set.range j) (hproper : Z ≠ Set.univ) :
    let I := (i ≫ j).ker
    let hI := supported_center_kernel_ne_bot i j Z hZ hCZ hZU hproper
    IsIntegral (GlobalBlowup.Data.Construction.globalBlowup I hI) ∧ IsProper (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ∧
      (∃ e : (GlobalBlowup.Data.Construction.globalBlowup I hI).PartialIso X,
        e.source.ι ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = e.iso.hom ≫ e.target.ι) ∧
      IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ ⟨Zᶜ, hZ.isOpen_compl⟩) := by
  let I := (i ≫ j).ker
  let hI := supported_center_kernel_ne_bot i j Z hZ hCZ hZU hproper
  refine ⟨inferInstance, inferInstance, GlobalBlowup.Data.Construction.globalBlowup_partialIso I hI, ?_⟩
  let : IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ I.support.compl) :=
    Blowup.Complement.Construction.globalBlowup_supportComplement_isIso I hI
  apply Blowup.Complement.Construction.isIso_restrict_of_le (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
    (V := I.support.compl)
  intro x hx
  change x ∉ (I.support : Set X)
  intro hxI
  have hsupport := supported_center_kernel_support i j Z hZ hCZ hZU
  change ((i ≫ j).ker.support : Set X) = Set.range (i ≫ j) at hsupport
  have hxr : x ∈ Set.range (i ≫ j) := hsupport ▸ hxI
  exact hx (hCZ hxr)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SupportedGlobalCenter.Construction
