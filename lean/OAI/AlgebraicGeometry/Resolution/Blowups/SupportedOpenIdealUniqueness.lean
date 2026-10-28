import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderSequenceExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing

/-! # Supported Open Ideal Uniqueness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SupportedOpenIdealUniqueness.Construction

noncomputable section

/-! A supported ideal is determined by its exact restriction to an open containing its support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_le_of_supported_open
    {V X : Scheme} [IsLocallyNoetherian X] (j : V ⟶ X) [IsOpenImmersion j]
    (I J : X.IdealSheafData) (hJ : (J.support : Set X) ⊆ Set.range j)
    (hlocal : I.comap j ≤ J.comap j) : I ≤ J := by
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian j
  apply (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_eq_top_iff J I).mp
  apply Global.OrderSequenceExtension.Construction.idealSheaf_eq_top_of_support_in_open j
  · intro x hx
    exact hJ (Scheme.IdealSheafData.support_antitone (NoetherianIdealSheafColon.Construction.le_noetherianIdealSheafColon J I) hx)
  · rw [IdealSheaf.ColonRestriction.Construction.noetherianIdealSheafColon_comap_open]
    exact (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_eq_top_iff _ _).mpr hlocal

theorem idealSheaf_eq_of_supported_open
    {V X : Scheme} [IsLocallyNoetherian X] (j : V ⟶ X) [IsOpenImmersion j]
    (I J : X.IdealSheafData) (hI : (I.support : Set X) ⊆ Set.range j)
    (hJ : (J.support : Set X) ⊆ Set.range j) (hlocal : I.comap j = J.comap j) : I = J :=
  le_antisymm (idealSheaf_le_of_supported_open j I J hJ hlocal.le)
    (idealSheaf_le_of_supported_open j J I hI hlocal.ge)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SupportedOpenIdealUniqueness.Construction
