import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Noetherian.Basic

/-! # Colon Localization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ColonLocalization.Construction

noncomputable section

/-! Localization of ideal quotients by finitely generated ideals. -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]

include M

/-- Localization commutes with an ideal quotient by one element, without
assuming that the element is regular or divides the ideal. -/
theorem localization_map_colon_singleton (J : Ideal R) (c : R) :
    (J.colon {c}).map (algebraMap R S) =
      (J.map (algebraMap R S)).colon {algebraMap R S c} := by
  ext x
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq M x
  rw [IsLocalization.mk'_mem_iff, IsLocalization.mk'_mem_iff,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M S,
    Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M S]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc]

/-- Localization commutes with an ideal quotient by a finite family. -/
theorem localization_map_colon_finite (J : Ideal R) (s : Set R) (hs : s.Finite) :
    (J.colon s).map (algebraMap R S) =
      (J.map (algebraMap R S)).colon ((algebraMap R S) '' s) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty => simp only [Submodule.colon_empty, Set.image_empty, Ideal.map_top]
  | @insert c s hc hs ih =>
    rw [Set.insert_eq, Submodule.colon_union, IsLocalization.map_inf M S,
      Set.image_union, Set.image_singleton, Submodule.colon_union,
      localization_map_colon_singleton M J c, ih]

/-- The ideal quotient of a coherent ideal by a finitely generated ideal
commutes with the actual localization map. -/
theorem localization_map_colon_fg (J K : Ideal R) (hK : K.FG) :
    (J.colon (K : Set R)).map (algebraMap R S) =
      (J.map (algebraMap R S)).colon (K.map (algebraMap R S) : Set S) := by
  obtain ⟨s, rfl⟩ := hK
  rw [Ideal.map_span, Ideal.colon_span, Ideal.colon_span]
  exact localization_map_colon_finite M J (s : Set R) s.finite_toSet

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ColonLocalization.Construction
