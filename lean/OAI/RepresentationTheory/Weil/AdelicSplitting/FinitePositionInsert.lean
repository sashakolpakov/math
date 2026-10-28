import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedTestFamilies

/-! # Finite Position Insert -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

section

/-! The finite part of a restricted Bruhat family is an actual locally
constant function on finite-adelic position space. Its infinite product is
a finite product multiplied by the integral-tail indicator. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def FinitePositionInsert.Construction.finiteIntegralTail (s : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  {a | ∀ i, ∀ v ∉ s, a i v ∈ v.adicCompletionIntegers F}

theorem FinitePositionInsert.Construction.finiteIntegralTail_clopen (s : Finset (HeightOneSpectrum (𝓞 F))) :
    IsClopen (FinitePositionInsert.Construction.finiteIntegralTail F N s) := by
  constructor
  · simp only [FinitePositionInsert.Construction.finiteIntegralTail, Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro _
    exact (Valued.isClosed_integer (v.adicCompletion F)).preimage
      ((RestrictedProduct.continuous_eval v).comp (continuous_apply i))
  · simp only [FinitePositionInsert.Construction.finiteIntegralTail, Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    have hh : IsOpen {x : ArchimedeanAdeles.Construction.FiniteAdeles F | ∀ v ∉ s, x v ∈ v.adicCompletionIntegers F} :=
      RestrictedProduct.isOpen_forall_imp_mem
        (fun v : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring (v.adicCompletion F))
        (p := fun v => v ∉ s)
    have hpre : IsOpen {a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F | ∀ v ∉ s, a i v ∈ v.adicCompletionIntegers F} :=
      hh.preimage (continuous_apply i : Continuous (fun a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F => a i))
    simpa only [Set.ofPred_forall] using hpre

def RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) : ℂ :=
  ∏' v : HeightOneSpectrum (𝓞 F), (f (.inr v)).val (fun i => a i v)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finite_localValue_eventually_one
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (f (.inr v)).val (fun i => a i v) = 1 := by
  have hi : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ i, a i v ∈ v.adicCompletionIntegers F :=
    eventually_all.mpr (fun i => (a i).property)
  filter_upwards [f.unramified, hi] with v hv hint
  rw [hv]
  exact RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ hint

theorem FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral (v : HeightOneSpectrum (𝓞 F))
    (x : Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N) (hx : ¬ ∀ i, x i ∈ v.adicCompletionIntegers F) :
    (Vacuum.Construction.finiteVacuum F N v).val x = 0 := by
  change (Vacuum.Construction.finitePositionLattice F N v).indicator (fun _ => (1 : ℂ)) x = 0
  apply Set.indicator_of_notMem
  exact fun h => hx (fun i => h i (Set.mem_univ i))

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue_formula
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (hs : ∀ v ∉ s, f (.inr v) = Vacuum.Construction.finiteVacuum F N v) (a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    f.finiteValue F N a =
      (∏ v ∈ s, (f (.inr v)).val (fun i => a i v)) *
        (FinitePositionInsert.Construction.finiteIntegralTail F N s).indicator (fun _ => (1 : ℂ)) a := by
  by_cases ha : a ∈ FinitePositionInsert.Construction.finiteIntegralTail F N s
  · rw [Set.indicator_of_mem ha, mul_one]
    apply HasProd.tprod_eq
    apply hasProd_prod_of_ne_finset_one
    intro v hv
    rw [hs v hv]
    exact RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v _ (fun i => ha i v hv)
  · rw [Set.indicator_of_notMem ha, mul_zero]
    apply tprod_of_exists_eq_zero
    have hh : ¬ ∀ v ∉ s, ∀ i, a i v ∈ v.adicCompletionIntegers F := by
      intro h
      exact ha (fun i v hv => h v hv i)
    push Not at hh
    obtain ⟨v, hv, i, hi⟩ := hh
    refine ⟨v, ?_⟩
    rw [hs v hv]
    exact FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ (fun h => hi (h i))

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue_locallyConstant (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    IsLocallyConstant (f.finiteValue F N) := by
  have hs := eventually_cofinite.mp f.unramified
  let s := hs.toFinset
  have houtside : ∀ v ∉ s, f (.inr v) = Vacuum.Construction.finiteVacuum F N v := by
    intro v hv
    simpa [s] using hv
  have hprod (t : Finset (HeightOneSpectrum (𝓞 F))) :
      IsLocallyConstant (fun a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F => ∏ v ∈ t, (f (.inr v)).val (fun i => a i v)) := by
    induction t using Finset.induction_on with
    | empty => simpa using! (IsLocallyConstant.const (X := Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) (1 : ℂ))
    | @insert v t hv ih =>
      simp only [Finset.prod_insert hv]
      have hl := (NonarchimedeanIntertwiner.LocalAnalysis.schwartzBruhat_totallyDisconnected_iff.mp (f (.inr v)).property).1
      exact (hl.comp_continuous (continuous_pi (fun i =>
        (RestrictedProduct.continuous_eval v).comp (continuous_apply i)))).mul ih
  have htail := (LocallyConstant.charFn ℂ (FinitePositionInsert.Construction.finiteIntegralTail_clopen F N s)).isLocallyConstant
  have he : f.finiteValue F N = fun a => (∏ v ∈ s, (f (.inr v)).val (fun i => a i v)) *
      (FinitePositionInsert.Construction.finiteIntegralTail F N s).indicator (fun _ => (1 : ℂ)) a :=
    funext (f.finiteValue_formula F N s houtside)
  rw [he]
  exact (hprod s).mul htail

end

/-! Inserting finitely many local position vectors into the actual finite
adeles, with zero in the remaining coordinates. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def FinitePositionInsert.Construction.finitePositionInsert (s : Finset (HeightOneSpectrum (𝓞 F)))
    (x : ∀ v : s, Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v.val)) N) : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F := fun i =>
  ⟨fun v => if hv : v ∈ s then x ⟨v, hv⟩ i else 0, by
    filter_upwards [s.finite_toSet.compl_mem_cofinite] with v hv
    change v ∉ s at hv
    rw [dite_eq_right hv]
    exact (v.adicCompletionIntegers F).zero_mem⟩

theorem FinitePositionInsert.Construction.finitePositionInsert_same (s : Finset (HeightOneSpectrum (𝓞 F)))
    (x : ∀ v : s, Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v.val)) N) (v : s) (i : Fin N) :
    FinitePositionInsert.Construction.finitePositionInsert F N s x i v.val = x v i := by
  change (if hv : v.val ∈ s then x ⟨v.val, hv⟩ i else (0 : ArchimedeanAdeles.Construction.Completion F (.inr v.val))) = x v i
  rw [dite_eq_left v.property]

theorem FinitePositionInsert.Construction.finitePositionInsert_other (s : Finset (HeightOneSpectrum (𝓞 F)))
    (x : ∀ v : s, Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v.val)) N)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ s) (i : Fin N) :
    FinitePositionInsert.Construction.finitePositionInsert F N s x i v = 0 := by
  change (if hv : v ∈ s then x ⟨v, hv⟩ i else (0 : ArchimedeanAdeles.Construction.Completion F (.inr v))) = 0
  rw [dite_eq_right hv]

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue_insert (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (s : Finset (HeightOneSpectrum (𝓞 F))) (hs : ∀ v ∉ s, f (.inr v) = Vacuum.Construction.finiteVacuum F N v)
    (x : ∀ v : s, Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v.val)) N) :
    f.finiteValue F N (FinitePositionInsert.Construction.finitePositionInsert F N s x) = ∏ v : s, (f (.inr v.val)).val (x v) := by
  have ht : FinitePositionInsert.Construction.finitePositionInsert F N s x ∈ FinitePositionInsert.Construction.finiteIntegralTail F N s := by
    intro i v hv
    rw [FinitePositionInsert.Construction.finitePositionInsert_other F N s x v hv i]
    exact (v.adicCompletionIntegers F).zero_mem
  rw [f.finiteValue_formula F N s hs, Set.indicator_of_mem ht, mul_one]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg (f (.inr v.val)).val
  funext i
  exact FinitePositionInsert.Construction.finitePositionInsert_same F N s x v i

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
