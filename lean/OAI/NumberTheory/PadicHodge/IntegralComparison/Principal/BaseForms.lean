import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseDerivation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham

/-! # Base Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseForms

noncomputable section

/-! Actual divided-power forms equal ordinary relative forms for a principal base ideal. -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def updateDerivation (n : ℕ) (v : Fin n → A) (i : Fin n) :
    Derivation R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  Derivation.mk' ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbols R A n).toMultilinearMap.toLinearMap v i)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_mul R A v i)

variable (r : R) (δR : DividedPowers (Ideal.span {r}))
  (δA : DividedPowers (Ideal.span {algebraMap R A r}))
  (hδ : DividedPowers.IsDPMorphism δR δA (algebraMap R A))

include hδ in
theorem relation_zero (n : ℕ) (t : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.RelationIndex A (Ideal.span {algebraMap R A r}) n) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation R A (Ideal.span {algebraMap R A r}) δA n t = 0 := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation, sub_eq_zero, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A (δA.dpow t.m t.x)]
  exact BaseDerivation.compatible R A r δR δA hδ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)
    (updateDerivation R A n t.v t.i) t.m t.x t.x.property

include hδ in
theorem relations_eq_bot (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A (Ideal.span {algebraMap R A r}) δA n = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨t, rfl⟩
  exact (Submodule.mem_bot _).mpr (relation_zero R A r δR δA hδ n t)

def formsEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A (Ideal.span {algebraMap R A r}) δA n ≃ₗ[A]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A (Ideal.span {algebraMap R A r}) δA n).quotEquivOfEqBot
    (relations_eq_bot R A r δR δA hδ n)

theorem formsEquiv_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsEquiv R A r δR δA hδ n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A (Ideal.span {algebraMap R A r}) δA a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ _

theorem differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A (Ideal.span {algebraMap R A r}) δA n) :
    formsEquiv R A r δR δA hδ (n + 1)
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A (Ideal.span {algebraMap R A r}) δA n ω) =
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n (formsEquiv R A r δR δA hδ n ω) := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A (Ideal.span {algebraMap R A r}) δA n) ω
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_mk]
  exact (Submodule.quotEquivOfEqBot_apply_mk _ _ _).trans
    (congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n) (Submodule.quotEquivOfEqBot_apply_mk _ _ _).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseForms
