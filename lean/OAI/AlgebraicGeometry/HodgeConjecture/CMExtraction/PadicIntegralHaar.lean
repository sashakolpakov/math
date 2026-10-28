import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Unipotent
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # Padic Integral Haar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralHaar.Iwasawa

noncomputable section

/-! The actual p-adic integer subset is compact and open. Its normalized
additive Haar measure supplies the auxiliary integral choice internally. -/

open _root_.MeasureTheory _root_.TopologicalSpace

variable (q : ℕ) [Fact q.Prime]

theorem padicIntegralSet_compact : IsCompact (Unipotent.Iwasawa.padicIntegralSet q) := by
  let : CompactSpace ℤ_[q] := PadicInt.compactSpace q
  change IsCompact (Set.range (fun x : ℤ_[q] => (x : ℚ_[q])))
  exact isCompact_range (show Continuous (fun x : ℤ_[q] => (x : ℚ_[q])) from
    (PadicInt.isOpenEmbedding_coe (p := q)).continuous)

theorem padicIntegralSet_open : IsOpen (Unipotent.Iwasawa.padicIntegralSet q) :=
  PadicInt.isOpenEmbedding_coe.isOpen_range

def padicIntegralPositiveCompact : PositiveCompacts ℚ_[q] where
  carrier := Unipotent.Iwasawa.padicIntegralSet q
  isCompact' := padicIntegralSet_compact q
  interior_nonempty' := by
    rw [(padicIntegralSet_open q).interior_eq]
    exact ⟨0, 0, map_zero (PadicInt.Coe.ringHom (p := q))⟩

variable [MeasurableSpace ℚ_[q]] [BorelSpace ℚ_[q]]

def padicIntegralHaar : Measure ℚ_[q] := Measure.addHaarMeasure (padicIntegralPositiveCompact q)

instance padicIntegralHaar_invariant : (padicIntegralHaar q).IsAddLeftInvariant :=
  inferInstanceAs ((Measure.addHaarMeasure (padicIntegralPositiveCompact q)).IsAddLeftInvariant)

theorem padicIntegralHaar_volume : padicIntegralHaar q (Unipotent.Iwasawa.padicIntegralSet q) = 1 :=
  Measure.addHaarMeasure_self

omit [MeasurableSpace ℚ_[q]] [BorelSpace ℚ_[q]] in
theorem padic_residue_card : Nat.card (IsLocalRing.ResidueField ℤ_[q]) = q := by
  rw [Nat.card_congr PadicInt.residueField.toEquiv]
  simp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralHaar.Iwasawa
