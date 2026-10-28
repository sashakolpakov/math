import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionExtension

/-! # Global Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Uniform positive-degree global extensions for finitely many local functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated]

/-- Global extension works in every degree beyond a positive threshold. -/
theorem Line.Bundles.LineBundle.section_extension_eventually (L : Line.Bundles.LineBundle Y)
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n), ∀ m : ℕ, n ≤ m →
      ∃ a : Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf m, Global.SectionExtension.PowerExtends s r m a := by
  obtain ⟨n, hn, a, ha⟩ := L.section_extension s r
  refine ⟨n, hn, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact ⟨a ≫ Power.SectionTransitions.powerSectionTransition s n k, Global.SectionExtension.PowerExtends.transition s r n k a ha⟩

/-- Finitely many functions, possibly on different nonvanishing opens, have
global numerators in one common positive tensor power. -/
theorem Line.Bundles.LineBundle.sections_extension_uniform (L : Line.Bundles.LineBundle Y) {ι : Type v} [Finite ι]
    (s : ι → (Line.Bundles.structureModule Y ⟶ L.sheaf))
    (r : ∀ i, Γ((Ample.LineBundles.sectionNonvanishing (s i)).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n) (a : ι → (Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)),
      ∀ i, Global.SectionExtension.PowerExtends (s i) (r i) n (a i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose n _hn h using fun i => L.section_extension_eventually (s i) (r i)
  let m := Finset.univ.sup n + 1
  have hm (i : ι) : n i ≤ m :=
    (Finset.le_sup (f := n) (Finset.mem_univ i)).trans (Nat.le_succ _)
  choose a ha using fun i => h i m (hm i)
  exact ⟨m, Nat.zero_lt_succ _, a, ha⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
