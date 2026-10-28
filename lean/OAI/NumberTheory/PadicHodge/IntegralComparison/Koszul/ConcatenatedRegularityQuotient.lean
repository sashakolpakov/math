import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ConcatenatedRegularity

/-! # Concatenated Regularity Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ConcatenatedRegularityQuotient

noncomputable section

/-! The quotient tail of an actual weakly regular concatenated tuple
is weakly regular over its quotient ring. -/
open RingTheory.Sequence
universe u
variable {A : Type u} [CommRing A]

theorem quotient_of_append_list (I : Ideal A) (s t : List A)
    (hI : Ideal.ofList s = I) (hst : IsWeaklyRegular A (s ++ t)) :
    IsWeaklyRegular (A ⧸ I) (t.map (Ideal.Quotient.mk I)) := by
  have ht := ((isWeaklyRegular_append_iff A s t).mp hst).2
  have he : (Ideal.ofList s • (⊤ : Ideal A)) = I := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hI]
  let e := Submodule.quotEquivOfEq _ _ he
  have hq : IsWeaklyRegular (A ⧸ I) t := (e.isWeaklyRegular_congr t).mp ht
  exact (isWeaklyRegular_map_algebraMap_iff (A ⧸ I) (A ⧸ I) t).mpr hq

theorem quotient_of_append (I : Ideal A) {c m : ℕ} (s : Fin c → A) (t : Fin m → A)
    (hI : Ideal.span (Set.range s) = I)
    (hst : IsWeaklyRegular A (List.ofFn (Fin.append s t))) :
    IsWeaklyRegular (A ⧸ I) (List.ofFn (fun i => Ideal.Quotient.mk I (t i))) := by
  have h := quotient_of_append_list I (List.ofFn s) (List.ofFn t)
    (by rw [Smooth.RegularSequence.CoordinateRegularity.ofList_ofFn]; exact hI)
    (by simpa only [List.ofFn_fin_append] using hst)
  simpa only [List.map_ofFn, Function.comp_def] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ConcatenatedRegularityQuotient
