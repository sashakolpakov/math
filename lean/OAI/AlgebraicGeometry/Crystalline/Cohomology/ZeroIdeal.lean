import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms
import Mathlib.RingTheory.Kaehler.Basic

/-! # Zero Ideal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms

noncomputable section

/-!
# Ordinary forms as the zero-ideal PD de Rham complex

For the zero ideal, all differential divided-power relations already
vanish. The actual quotient complex is therefore isomorphic to ordinary
algebraic forms, over any commutative ring. Its degree-one universal
property identifies the forms with actual Kähler differentials.
-/

open _root_.CategoryTheory

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

local notation "I" => (⊥ : Ideal A)
local notation "δ" => dividedPowersBot A

theorem relation_zero (n : ℕ) (t : PD.DeRham.PDDeRham.RelationIndex A I n) :
    PD.DeRham.PDDeRham.relation R A I δ n t = 0 := by
  have hx : (t.x : A) = 0 := t.x.property
  have hz : DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (Function.update t.v t.i 0) = 0 := by
    simpa only [map_zero] using DeRhamPresentationTo.DeRhamPresentation.symbol_update_base R A t.v t.i (0 : R)
  rw [PD.DeRham.PDDeRham.relation, hx, (δ).dpow_eval_zero (Nat.succ_ne_zero t.m), hz,
    DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one, hz, smul_zero, sub_self]

theorem relations_eq_bot (n : ℕ) : PD.DeRham.PDDeRham.relations R A I δ n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact (relation_zero R A n t) ▸ Submodule.zero_mem _

def formsEquiv (n : ℕ) : PD.DeRham.PDDeRham.Form R A I δ n ≃ₗ[A] DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  (PD.DeRham.PDDeRham.relations R A I δ n).quotEquivOfEqBot (relations_eq_bot R A n)

theorem formsEquiv_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsEquiv R A n (PD.DeRham.PDDeRham.symbol R A I δ a v) = DeRhamPresentationTo.DeRhamPresentation.symbol R A a v :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ _

theorem formsEquiv_symm_mk (n : ℕ) : (formsEquiv R A n).symm.toLinearMap =
    (PD.DeRham.PDDeRham.relations R A I δ n).mkQ :=
  Submodule.coe_quotEquivOfEqBot_symm _ _

def complexIso : DeRhamPresentationTo.DeRhamPresentation.complex R A ≅ PD.DeRham.PDDeRham.complex R A I δ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((formsEquiv R A n).symm.restrictScalars R).toModuleIso)
    (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      dsimp only [DeRhamPresentationTo.DeRhamPresentation.complex, PD.DeRham.PDDeRham.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      change (formsEquiv R A (n + 1)).symm (DeRhamPresentationTo.DeRhamPresentation.differential R A n t) =
        PD.DeRham.PDDeRham.differential R A I δ n ((formsEquiv R A n).symm t)
      rw [LinearEquiv.symm_apply_eq]
      change _ = formsEquiv R A (n + 1)
        (PD.DeRham.PDDeRham.differential R A I δ n ((formsEquiv R A n).symm t))
      rw [show (formsEquiv R A n).symm t = (PD.DeRham.PDDeRham.relations R A I δ n).mkQ t from
        LinearMap.congr_fun (formsEquiv_symm_mk R A n) t, PD.DeRham.PDDeRham.differential_mk]
      exact (Submodule.quotEquivOfEqBot_apply_mk _ _ _).symm)

theorem derivation_dpow (M : Type u) [AddCommGroup M] [Module A M] [Module R M]
    (d : Derivation R A M) (n : ℕ) (x : A) (hx : x ∈ I) :
    d ((δ).dpow (n + 1) x) = (δ).dpow n x • d x := by
  have hx0 : x = 0 := hx
  rw [hx0, (δ).dpow_eval_zero (Nat.succ_ne_zero n), map_zero, smul_zero]

def toKaehler : PD.DeRham.PDDeRham.Form R A I δ 1 →ₗ[A] KaehlerDifferential R A :=
  PD.OneForms.PDOneForms.lift R A I δ (KaehlerDifferential R A) (KaehlerDifferential.D R A)
    (derivation_dpow R A (KaehlerDifferential R A) (KaehlerDifferential.D R A))

def fromKaehler : KaehlerDifferential R A →ₗ[A] PD.DeRham.PDDeRham.Form R A I δ 1 :=
  (PD.OneForms.PDOneForms.D R A I δ).liftKaehlerDifferential

theorem toKaehler_D (a : A) : toKaehler R A (PD.OneForms.PDOneForms.D R A I δ a) = KaehlerDifferential.D R A a :=
  PD.OneForms.PDOneForms.lift_D R A I δ (KaehlerDifferential R A) (KaehlerDifferential.D R A)
    (derivation_dpow R A (KaehlerDifferential R A) (KaehlerDifferential.D R A)) a

theorem fromKaehler_D (a : A) : fromKaehler R A (KaehlerDifferential.D R A a) = PD.OneForms.PDOneForms.D R A I δ a :=
  Derivation.liftKaehlerDifferential_comp_D _ a

def oneFormsEquiv : PD.DeRham.PDDeRham.Form R A I δ 1 ≃ₗ[A] KaehlerDifferential R A :=
  LinearEquiv.ofLinearMap (toKaehler R A) (fromKaehler R A)
    (by
      apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
      intro a
      exact (congrArg (toKaehler R A) (fromKaehler_D R A a)).trans (toKaehler_D R A a))
    (by
      apply PD.OneForms.PDOneForms.linearMap_ext R A I δ
      intro a
      exact (congrArg (fromKaehler R A) (toKaehler_D R A a)).trans (fromKaehler_D R A a))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms
