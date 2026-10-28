import OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexIso
import OAI.NumberTheory.PadicHodge.PeriodInvariants.LinearExtension

/-! # Complex Extension -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexExtension

noncomputable section

/-! # A complex map extends through completion when the target is termwise complete -/

open _root_.CategoryTheory

universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (C D : CochainComplex (ModuleCat.{u} R) ℕ) (f : C ⟶ D)
  (hD : ∀ n, IsAdicComplete I (D.X n))

def extension : AdicCompletionContraction.complex I C ⟶ D :=
  ((AdicCompletionLinear.functor I).mapHomologicalComplex (.up ℕ)).map f ≫
    (ComplexIso.complexIso I D hD).inv

theorem extends_finite : ComplexIso.inclusion I C ≫ extension I C D f hD = f := by
  let e : D ≅ AdicCompletionContraction.complex I D := ComplexIso.complexIso I D hD
  let g : AdicCompletionContraction.complex I C ⟶ AdicCompletionContraction.complex I D :=
    ((AdicCompletionLinear.functor I).mapHomologicalComplex (.up ℕ)).map f
  have he : e.hom = ComplexIso.inclusion I D := ComplexIso.complexIso_hom I D hD
  have hn : ComplexIso.inclusion I C ≫ g = f ≫ e.hom :=
    (ComplexIso.inclusion_natural I C f).trans
      (congrArg (fun k : D ⟶ AdicCompletionContraction.complex I D => f ≫ k) he.symm)
  change ComplexIso.inclusion I C ≫ (g ≫ e.inv) = f
  rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexExtension
