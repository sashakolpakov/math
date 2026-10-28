import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets

/-! # Restricted Test Families -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedTestFamilies.Construction

noncomputable section

/-! Actual restricted families of local Bruhat test functions. Their values
are finite products at each adelic point, and the restricted oscillator
family acts componentwise while preserving the vacuum tail. -/

open scoped Classical _root_.NumberField
open Filter IsDedekindDomain

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

structure RestrictedTestFamily where
  component : ∀ v : ArchimedeanAdeles.Construction.Places F, Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N
  unramified : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    component (.inr v) = Vacuum.Construction.finiteVacuum F N v

instance restrictedTestFamilyCoeFun : CoeFun (RestrictedTestFamily F N)
    (fun _ => (v : ArchimedeanAdeles.Construction.Places F) → Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) := ⟨RestrictedTestFamily.component⟩

theorem finiteVacuum_eq_one_of_integral (v : HeightOneSpectrum (𝓞 F))
    (x : Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N) (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    (Vacuum.Construction.finiteVacuum F N v).val x = 1 := by
  change LocallyConstant.charFn ℂ (Vacuum.Construction.finitePositionLattice_clopen F N v) x = 1
  exact (LocallyConstant.charFn_eq_one ℂ x (Vacuum.Construction.finitePositionLattice_clopen F N v)).mpr (fun i _ => hx i)

def RestrictedTestFamily.localValue (f : RestrictedTestFamily F N) (a : Fin N → ArchimedeanAdeles.Construction.Adeles F) (v : ArchimedeanAdeles.Construction.Places F) : ℂ :=
  (f v).val (fun i => ArchimedeanAdeles.Construction.evaluate F v (a i))

theorem RestrictedTestFamily.localValue_eventually_one
    (f : RestrictedTestFamily F N) (a : Fin N → ArchimedeanAdeles.Construction.Adeles F) :
    ∀ᶠ v : ArchimedeanAdeles.Construction.Places F in cofinite, f.localValue F N a v = 1 := by
  have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ i, (a i).2 v ∈ v.adicCompletionIntegers F :=
    eventually_all.mpr (fun i => (a i).2.property)
  have hfin : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      f.localValue F N a (.inr v) = 1 := by
    filter_upwards [f.unramified, hint] with v hv hi
    change (f (.inr v)).val (fun i => (a i).2 v) = 1
    rw [hv]
    exact finiteVacuum_eq_one_of_integral F N v _ hi
  have hnonarch : ∀ᶠ v : ArchimedeanAdeles.Construction.Places F in cofinite,
      v ∉ Set.range (Sum.inl : NumberField.InfinitePlace F → ArchimedeanAdeles.Construction.Places F) :=
    (Set.finite_range (Sum.inl : NumberField.InfinitePlace F → ArchimedeanAdeles.Construction.Places F)).compl_mem_cofinite
  have htail := UnramifiedCharacter.Construction.eventually_cofinite_sum_right
    (I := NumberField.InfinitePlace F) (fun v => f.localValue F N a (.inr v) = 1) hfin
  filter_upwards [hnonarch, htail] with v hv ht
  cases v with
  | inl v => exact (hv ⟨v, rfl⟩).elim
  | inr v => exact ht

def RestrictedTestFamily.value (f : RestrictedTestFamily F N) (a : Fin N → ArchimedeanAdeles.Construction.Adeles F) : ℂ :=
  ∏' v, f.localValue F N a v

theorem RestrictedTestFamily.localValue_hasProd
    (f : RestrictedTestFamily F N) (a : Fin N → ArchimedeanAdeles.Construction.Adeles F) :
    HasProd (f.localValue F N a) (f.value F N a) := by
  apply Multipliable.hasProd
  exact multipliable_of_hasFiniteMulSupport
    (eventually_cofinite.mp (f.localValue_eventually_one F N a))

def RestrictedTestFamily.act (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (a : Rational.Construction.RestrictedCover F N ψ) (f : RestrictedTestFamily F N) : RestrictedTestFamily F N where
  component v := Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) (f v)
  unramified := by
    have hprop : ∀ᶠ v : ArchimedeanAdeles.Construction.Places F in cofinite, a v ∈ Vacuum.Construction.coverIntegral F N ψ v := a.property
    have ha : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
        a (.inr v) ∈ Vacuum.Construction.coverIntegral F N ψ (.inr v) :=
      Sum.inr_injective.tendsto_cofinite.eventually hprop
    filter_upwards [ha, f.unramified] with v hv hf
    rw [hf]
    exact hv.2

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedTestFamilies.Construction
