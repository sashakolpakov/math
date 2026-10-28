import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Nonzero -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero.Construction

noncomputable section

/-! Nonzero ideals remain nonzero under actual global blowups in every dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Compatibility with a dense partial isomorphism makes the actual map dominant. -/
theorem isDominant_of_compatible_partialIso {Y X : Scheme.{u}} (π : Y ⟶ X)
    (e : Y.PartialIso X) (he : e.source.ι ≫ π = e.iso.hom ≫ e.target.ι) :
    IsDominant π := by
  let : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  have h : IsDominant (e.source.ι ≫ π) := he.symm ▸ inferInstance
  let : IsDominant (e.source.ι ≫ π) := h
  exact IsDominant.of_comp e.source.ι π

/-- Pullback along a morphism with zero kernel cannot annihilate a nonzero
native ideal sheaf. This uses the actual pullback-pushforward adjunction. -/
theorem idealSheaf_comap_ne_bot_of_ker_eq_bot {Y X : Scheme.{u}} (π : Y ⟶ X)
    (hker : π.ker = ⊥) (J : X.IdealSheafData) (hJ : J ≠ ⊥) : J.comap π ≠ ⊥ := by
  intro he
  have h := Scheme.IdealSheafData.le_map_comap J π
  rw [he, Scheme.IdealSheafData.map_bot, hker] at h
  exact hJ (le_bot_iff.mp h)

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

instance globalBlowupToBase_isDominant (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsDominant (Data.Construction.globalBlowupToBase I hI) := by
  obtain ⟨e, he⟩ := Data.Construction.globalBlowup_partialIso I hI
  exact isDominant_of_compatible_partialIso (Data.Construction.globalBlowupToBase I hI) e he

instance globalBlowupToBase_isSchemeTheoreticallyDominant (I : X.IdealSheafData)
    (hI : I ≠ ⊥) : IsSchemeTheoreticallyDominant (Data.Construction.globalBlowupToBase I hI) :=
  IsSchemeTheoreticallyDominant.of_isDominant (Data.Construction.globalBlowupToBase I hI)

/-- Properness and the proved dense range imply surjectivity of the actual blowup map. -/
instance globalBlowupToBase_surjective (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Surjective (Data.Construction.globalBlowupToBase I hI) :=
  surjective_of_isDominant_of_isClosed_range (Data.Construction.globalBlowupToBase I hI)
    (Data.Construction.globalBlowupToBase I hI).isClosedMap.isClosed_range

/-- The actual total transform remains nonzero in arbitrary dimension. -/
theorem globalBlowup_totalIdeal_ne_bot (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) : J.comap (Data.Construction.globalBlowupToBase I hI) ≠ ⊥ :=
  idealSheaf_comap_ne_bot_of_ker_eq_bot (Data.Construction.globalBlowupToBase I hI)
    (Data.Construction.globalBlowupToBase I hI).ker_eq_bot J hJ

/-- The native controlled ideal remains nonzero in arbitrary dimension,
so it is an admissible input ideal for a subsequent actual blowup. -/
theorem globalBlowupControlledIdeal_ne_bot (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (b : ℕ) (hJ : J ≠ ⊥) : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b ≠ ⊥ :=
  GlobalControlled.Ideal.Construction.controlledIdealSheaf_ne_bot I J b (Data.Construction.globalBlowupToBase I hI)
    (globalBlowup_totalIdeal_ne_bot I J hI hJ)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero.Construction
