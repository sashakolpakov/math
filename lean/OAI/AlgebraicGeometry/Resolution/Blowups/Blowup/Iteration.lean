import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement

/-! # Iteration -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Iteration.Construction

noncomputable section

/-! Preservation of the original smooth locus under successive blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The global blowup remains locally Noetherian, so the construction can be iterated. -/
instance globalBlowup_locallyNoetherian {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsLocallyNoetherian (GlobalBlowup.Data.Construction.globalBlowup I hI) :=
  LocallyOfFiniteType.isLocallyNoetherian (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)

/-- The restriction of a finitely presented morphism to its smooth locus is smooth. -/
theorem smooth_on_smoothLocus_general {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  ext x
  simp

/-- An isomorphism over the original smooth locus puts its inverse image
inside the smooth locus of the composite structural morphism. -/
theorem smoothLocus_preimage_le_of_isIso_restrict {Y X S : Scheme.{u}}
    (π : Y ⟶ X) (f : X ⟶ S) [LocallyOfFinitePresentation π] [LocallyOfFinitePresentation f]
    [IsIso (π ∣_ f.smoothLocus)] :
    π ⁻¹ᵁ f.smoothLocus ≤ (π ≫ f).smoothLocus := by
  let : Smooth (f.smoothLocus.ι ≫ f) := smooth_on_smoothLocus_general f
  have hcomp : (π ⁻¹ᵁ f.smoothLocus).ι ≫ (π ≫ f) =
      (π ∣_ f.smoothLocus) ≫ (f.smoothLocus.ι ≫ f) := by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  let : Smooth ((π ⁻¹ᵁ f.smoothLocus).ι ≫ (π ≫ f)) := hcomp.symm ▸ inferInstance
  have heq : (π ⁻¹ᵁ f.smoothLocus).ι ⁻¹ᵁ (π ≫ f).smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq (π ⁻¹ᵁ f.smoothLocus).ι (π ≫ f),
      Scheme.Hom.smoothLocus_eq_top ((π ⁻¹ᵁ f.smoothLocus).ι ≫ (π ≫ f))]
  intro y hy
  have hm : (⟨y, hy⟩ : (π ⁻¹ᵁ f.smoothLocus).toScheme) ∈
      (π ⁻¹ᵁ f.smoothLocus).ι ⁻¹ᵁ (π ≫ f).smoothLocus := by
    rw [heq]
    trivial
  exact hm

/-- A further blowup inside the current singular locus preserves the
isomorphism over the original smooth locus. -/
theorem globalBlowup_step_preserves_smoothLocus {Y X S : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (π : Y ⟶ X) (f : X ⟶ S) [LocallyOfFinitePresentation π] [LocallyOfFinitePresentation f]
    [IsIso (π ∣_ f.smoothLocus)] (I : Y.IdealSheafData) (hI : I ≠ ⊥)
    (hcenter : (I.support : Set Y) ⊆ ((π ≫ f).smoothLocus : Set Y)ᶜ) :
    IsIso ((GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ π) ∣_ f.smoothLocus) := by
  have hdisjoint : π ⁻¹ᵁ f.smoothLocus ≤ I.support.compl := by
    intro y hy
    exact fun hys => hcenter hys (smoothLocus_preimage_le_of_isIso_restrict π f hy)
  let : IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ π ⁻¹ᵁ f.smoothLocus) :=
    Complement.Construction.globalBlowup_isIso_on_open I hI _ hdisjoint
  exact (morphismRestrict_comp (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) π f.smoothLocus).symm ▸
    (inferInstance : IsIso ((GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ π ⁻¹ᵁ f.smoothLocus) ≫
      (π ∣_ f.smoothLocus)))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Iteration.Construction
