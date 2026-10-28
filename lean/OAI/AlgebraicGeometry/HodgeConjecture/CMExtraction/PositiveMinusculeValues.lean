import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralTransform
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralHaar

/-! # Positive Minuscule Values -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PositiveMinusculeValues.Iwasawa

noncomputable section

/-! CosetCalculus computes the two minuscule values of the actual GL3 torus
character. The normalized Haar measure and finite residue field are
constructed here; neither is an extra hypothesis. -/

open scoped _root_.Matrix
open _root_.MeasureTheory

variable (q : ℕ) [Fact q.Prime]

theorem gl3Torus_positive_first (t : Fin 3 → ℂˣ) :
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (IntegralTransform.Iwasawa.positiveGL3Hecke q ![1, 0, 0]) =
      (q : ℂ) * ((t 0 : ℂ) + (t 1 : ℂ) + (t 2 : ℂ)) := by
  let : MeasurableSpace ℚ_[q] := borel _
  let : BorelSpace ℚ_[q] := ⟨rfl⟩
  let : Finite (IsLocalRing.ResidueField ℤ_[q]) :=
    Finite.of_equiv (ZMod q) PadicInt.residueField.symm.toEquiv
  rw [IntegralTransform.Iwasawa.gl3TorusSatakeOver_positive_integral q (PadicIntegralHaar.Iwasawa.padicIntegralHaar q)
    (PadicIntegralHaar.Iwasawa.padicIntegralSet_open q).measurableSet (PadicIntegralHaar.Iwasawa.padicIntegralHaar_volume q)]
  have h := RepresentationTheory.Hecke.Satake.CosetCalculus.satake_first_minuscule (q : ℤ_[q]) PadicInt.irreducible_p (PadicIntegralHaar.Iwasawa.padicIntegralHaar q)
    (PadicIntegralHaar.Iwasawa.padicIntegralSet_open q).measurableSet (PadicIntegralHaar.Iwasawa.padicIntegralHaar_volume q) t
  rwa [PadicIntegralHaar.Iwasawa.padic_residue_card] at h

theorem gl3Torus_positive_second (t : Fin 3 → ℂˣ) :
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (IntegralTransform.Iwasawa.positiveGL3Hecke q ![1, 1, 0]) =
      (q : ℂ) * ((t 0 : ℂ) * (t 1 : ℂ) + (t 0 : ℂ) * (t 2 : ℂ) + (t 1 : ℂ) * (t 2 : ℂ)) := by
  let : MeasurableSpace ℚ_[q] := borel _
  let : BorelSpace ℚ_[q] := ⟨rfl⟩
  let : Finite (IsLocalRing.ResidueField ℤ_[q]) :=
    Finite.of_equiv (ZMod q) PadicInt.residueField.symm.toEquiv
  rw [IntegralTransform.Iwasawa.gl3TorusSatakeOver_positive_integral q (PadicIntegralHaar.Iwasawa.padicIntegralHaar q)
    (PadicIntegralHaar.Iwasawa.padicIntegralSet_open q).measurableSet (PadicIntegralHaar.Iwasawa.padicIntegralHaar_volume q)]
  have h := RepresentationTheory.Hecke.Satake.CosetCalculus.satake_second_minuscule (q : ℤ_[q]) PadicInt.irreducible_p (PadicIntegralHaar.Iwasawa.padicIntegralHaar q)
    (PadicIntegralHaar.Iwasawa.padicIntegralSet_open q).measurableSet (PadicIntegralHaar.Iwasawa.padicIntegralHaar_volume q) t
  rwa [PadicIntegralHaar.Iwasawa.padic_residue_card] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PositiveMinusculeValues.Iwasawa
