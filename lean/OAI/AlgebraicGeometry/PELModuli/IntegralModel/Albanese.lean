import OAI.AlgebraicGeometry.Albanese.Construction.GeneratingWords
import Lean.Util.CollectAxioms

/-! # Albanese -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese

noncomputable section

/-!
The Albanese universal property forces generation by a fixed finite word in
point differences. `ConstructionInput` is exactly the supplied complex Albanese
existence proposition, exposed as a hypothesis instead of using its stub.
The geometric subgroup and dimension lemmas imported here have actual proofs.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

/-- Pointed Albanese universality, with the same group-object convention as Construction. -/
def IsAlbaneseMap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) : Prop :=
  x₀ ≫ a = 1 ∧
    ∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
      x₀ ≫ f = 1 → ∃! φ : A.toOver ⟶ B.toOver,
        IsMonHom φ ∧ a ≫ φ = f

/-- The complete supplied Construction proposition, without asserting it. -/
def ConstructionInput : Prop :=
  ∀ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver),
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
      IsAlbaneseMap X x₀ A a

/-- Universality rules out a proper abelian subvariety containing all
Albanese point differences. -/
theorem albanese_generates (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)
    (ha : IsAlbaneseMap X x₀ A a) : Albanese.Construction.GeneratedClosed.Generates X A a := by
  obtain ⟨B, b, j, hjclosed, hjhom, hb0, hb, hgen⟩ :=
    Albanese.Construction.GeneratedClosed.exists_generated_abelian_subvariety X x₀ A a ha.1
  let : IsClosedImmersion j.left := hjclosed
  let : IsMonHom j := hjhom
  obtain ⟨r, hr, _⟩ := ha.2 B b hb0
  let : IsMonHom r := hr.1
  have hrj : r ≫ j = 𝟙 A.toOver := by
    obtain ⟨u, _, hu⟩ := ha.2 A a ha.1
    have hleft : r ≫ j = u := hu _ ⟨inferInstance, by
      rw [← Category.assoc, hr.2, hb]⟩
    have hright : 𝟙 A.toOver = u := hu _ ⟨inferInstance, Category.comp_id a⟩
    exact hleft.trans hright.symm
  apply le_antisymm le_top
  intro p _
  apply (hgen p).mp
  exact ⟨p ≫ r, by rw [Category.assoc, hrj, Category.comp_id]⟩

/-- One positive finite number of differences already covers the whole
Albanese scheme; the number can be chosen as `dim A + 1`. -/
theorem albanese_finite_word_surjective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)
    (ha : IsAlbaneseMap X x₀ A a) :
    ∃ n : ℕ, 0 < n ∧ Surjective (Albanese.Construction.ImageWords.wordMap X A a n).left := by
  refine ⟨Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap + 1,
    Nat.succ_pos _, ?_⟩
  exact Albanese.Construction.GeneratingWords.generating_word_surjective X x₀ A a
    (albanese_generates X x₀ A a ha) _ (Nat.le_succ _)

/-- Construction implies the characteristic-zero generation assertion in IntegralModel,
with no generation hypothesis added to the input. -/
theorem exists_albanese_with_finite_word
    (hConstruction : ConstructionInput) (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
      IsAlbaneseMap X x₀ A a ∧
      ∃ n : ℕ, 0 < n ∧ Surjective (Albanese.Construction.ImageWords.wordMap X A a n).left := by
  obtain ⟨A, a, ha⟩ := hConstruction X x₀
  exact ⟨A, a, ha, albanese_finite_word_surjective X x₀ A a ha⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese
