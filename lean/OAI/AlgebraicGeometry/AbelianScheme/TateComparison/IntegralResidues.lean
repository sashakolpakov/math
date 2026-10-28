import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalCompletion
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitAction

/-! # Integral Residues -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralResidues.SphericalPELAlbaneseData

noncomputable section

/-! Complete splitting produces integral elements with arbitrary prescribed
finite local residues. In particular the split finite-level projectors are
realized by actual integral PEL endomorphisms, without a second q-adic choice. -/

open scoped TensorProduct Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (n : ℕ)

local instance : NeZero (q ^ n) := ⟨pow_ne_zero n (Fact.out : q.Prime).ne_zero⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.localResidueMap : NumberField.RingOfIntegers E →+* (Fin s × Bool → ZMod (q ^ n)) :=
  RingHom.pi fun v => (PadicInt.toZModPow n).comp (D.localCharacter v)

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.localResidueMap_apply (a : NumberField.RingOfIntegers E) (v : Fin s × Bool) :
    D.localResidueMap n a v = PadicInt.toZModPow n (D.localCharacter v a) := rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.completion_residue_has_integral_representative
    (t : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) :
    ∃ a : NumberField.RingOfIntegers E, ∀ v,
      PadicInt.toZModPow n (D.localCompletionMap t v) = D.localResidueMap n a v := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
    obtain ⟨a, ha⟩ := ht
    obtain ⟨b, hb⟩ := hu
    exact ⟨a + b, by intro v; simp only [map_add, Pi.add_apply, ha v, hb v]⟩
  | tmul z a =>
    refine ⟨(PadicInt.toZModPow n z).val • a, ?_⟩
    intro v
    simp only [Data.SphericalPELAlbaneseData.localCompletionMap_tmul, Data.SphericalPELAlbaneseData.localResidueMap_apply,
      nsmul_eq_mul, map_mul, map_natCast, ZMod.natCast_zmod_val]

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.localResidueMap_surjective (hg : D.IsGoodCompletelySplitPrime) :
    Function.Surjective (D.localResidueMap n) := by
  intro a
  obtain ⟨t, ht⟩ := hg.1.2 (fun v => ((a v).val : ℤ_[q]))
  obtain ⟨r, hr⟩ := D.completion_residue_has_integral_representative n t
  refine ⟨r, ?_⟩
  funext v
  rw [← hr v, ht, map_natCast, ZMod.natCast_zmod_val]

/-- An actual element of O_E realizing the v-th projector modulo q^n. -/
def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.integralResidueProjector (hg : D.IsGoodCompletelySplitPrime) (v : Fin s × Bool) :
    NumberField.RingOfIntegers E :=
  (D.localResidueMap_surjective n hg (Pi.single v 1)).choose

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.integralResidueProjector_residues (hg : D.IsGoodCompletelySplitPrime) (v w : Fin s × Bool) :
    PadicInt.toZModPow n (D.localCharacter w (D.integralResidueProjector n hg v)) =
      (Pi.single v 1 : Fin s × Bool → ZMod (q ^ n)) w :=
  congrFun (D.localResidueMap_surjective n hg (Pi.single v 1)).choose_spec w

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralResidues.SphericalPELAlbaneseData
