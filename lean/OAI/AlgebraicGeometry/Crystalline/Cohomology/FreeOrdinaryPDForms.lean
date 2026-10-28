import OAI.AlgebraicGeometry.Crystalline.Cohomology.TorsionFreeDerivation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormDerivation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham

/-! # Free Ordinary PD Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeOrdinaryPDForms.TorsionFreeOrdinaryPDForms

noncomputable section

/-!
# Existing divided powers impose no new relations on torsion-free ordinary forms

The derivative of the factorial identity verifies each actual
divided-power differential relation. The resulting quotient is the
original ordinary form module, compatibly with exterior differentiation.
-/

open _root_.CategoryTheory

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [IsDomain A] [CharZero A] [Algebra R A]
  [∀ n, Module.IsTorsionFree A (DeRhamPresentationTo.DeRhamPresentation.Form R A n)]
  (I : Ideal A) (δ : DividedPowers I)

theorem relation_zero (n : ℕ) (t : PD.DeRham.PDDeRham.RelationIndex A I n) :
    PD.DeRham.PDDeRham.relation R A I δ n t = 0 := by
  rw [PD.DeRham.PDDeRham.relation, DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A (δ.dpow t.m t.x), sub_eq_zero]
  exact TorsionFreeDerivation.TorsionFreePDDerivation.compatible R A (DeRhamPresentationTo.DeRhamPresentation.Form R A n) I δ
    (OrdinaryFormDerivation.OrdinaryFormSlots.derivation R A t.v t.i) t.m t.x t.x.property

theorem relations_eq_bot (n : ℕ) : PD.DeRham.PDDeRham.relations R A I δ n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact (relation_zero R A I δ n t) ▸ Submodule.zero_mem _

def formsEquiv (n : ℕ) : PD.DeRham.PDDeRham.Form R A I δ n ≃ₗ[A] DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  (PD.DeRham.PDDeRham.relations R A I δ n).quotEquivOfEqBot (relations_eq_bot R A I δ n)

theorem formsEquiv_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsEquiv R A I δ n (PD.DeRham.PDDeRham.symbol R A I δ a v) = DeRhamPresentationTo.DeRhamPresentation.symbol R A a v :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ _

theorem formsEquiv_symm_mk (n : ℕ) : (formsEquiv R A I δ n).symm.toLinearMap =
    (PD.DeRham.PDDeRham.relations R A I δ n).mkQ := Submodule.coe_quotEquivOfEqBot_symm _ _

def complexIso : DeRhamPresentationTo.DeRhamPresentation.complex R A ≅ PD.DeRham.PDDeRham.complex R A I δ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((formsEquiv R A I δ n).symm.restrictScalars R).toModuleIso)
    (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      dsimp only [DeRhamPresentationTo.DeRhamPresentation.complex, PD.DeRham.PDDeRham.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      change (formsEquiv R A I δ (n + 1)).symm (DeRhamPresentationTo.DeRhamPresentation.differential R A n t) =
        PD.DeRham.PDDeRham.differential R A I δ n ((formsEquiv R A I δ n).symm t)
      rw [LinearEquiv.symm_apply_eq]
      change _ = formsEquiv R A I δ (n + 1)
        (PD.DeRham.PDDeRham.differential R A I δ n ((formsEquiv R A I δ n).symm t))
      rw [show (formsEquiv R A I δ n).symm t = (PD.DeRham.PDDeRham.relations R A I δ n).mkQ t from
        LinearMap.congr_fun (formsEquiv_symm_mk R A I δ n) t, PD.DeRham.PDDeRham.differential_mk]
      exact (Submodule.quotEquivOfEqBot_apply_mk _ _ _).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeOrdinaryPDForms.TorsionFreeOrdinaryPDForms
