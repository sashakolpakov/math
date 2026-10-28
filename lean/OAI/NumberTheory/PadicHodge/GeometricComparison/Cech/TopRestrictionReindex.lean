import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IndexEquivalence

/-! # Top Restriction Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionReindex.CechTopRestrictionReindex

noncomputable section

/-! Cech index equivalence preserves the canonical top-section augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v a w z
variable (C : Type u) [SemilatticeInf C] [OrderTop C]
  {A : Type v} [Category.{a} A] [Preadditive A] [HasProducts.{w} A] [HasProducts.{z} A]
  {ι : Type w} {κ : Type z} (e : κ ≃ ι) (U : ι → C) (P : Cᵒᵖ ⥤ A)

theorem map : TopRestriction.CechTopRestriction.map C (U ∘ e) P ≫
    (IndexEquivalence.CechIndexEquivalence.complexIso e U P).hom.f 0 = TopRestriction.CechTopRestriction.map C U P := by
  change Pi.lift (f := IndexEquivalence.CechIndexEquivalence.coefficients U P 0 ∘ IndexEquivalence.CechIndexEquivalence.tuples e 0)
    (fun t => P.map (homOfLE (le_top : (∏ᶜ (U ∘ IndexEquivalence.CechIndexEquivalence.tuples e 0 t)) ≤ ⊤)).op) ≫
      (Pi.reindex (IndexEquivalence.CechIndexEquivalence.tuples e 0) (IndexEquivalence.CechIndexEquivalence.coefficients U P 0)).hom =
    Pi.lift (fun t : Fin 1 → ι => P.map (homOfLE (le_top : (∏ᶜ (U ∘ t)) ≤ ⊤)).op)
  apply Pi.hom_ext
  intro t
  obtain ⟨s, rfl⟩ := (IndexEquivalence.CechIndexEquivalence.tuples e 0).surjective t
  simp only [Category.assoc, Pi.reindex_hom_π, Pi.lift_comp_π]

def initialIso : TopRestriction.CechTopRestriction.initial C (U ∘ e) P ≅ TopRestriction.CechTopRestriction.initial C U P :=
  ShortComplex.isoMk (Iso.refl _)
    ((HomologicalComplex.eval A (.up ℕ) 0).mapIso (IndexEquivalence.CechIndexEquivalence.complexIso e U P))
    ((HomologicalComplex.eval A (.up ℕ) 1).mapIso (IndexEquivalence.CechIndexEquivalence.complexIso e U P))
    ((Category.id_comp _).trans (CechTopRestrictionReindex.map C e U P).symm)
    ((IndexEquivalence.CechIndexEquivalence.complexIso e U P).hom.comm 0 1)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionReindex.CechTopRestrictionReindex
