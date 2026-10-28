import OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
import OAI.RepresentationTheory.Theta.Adelic.TensorProjective

/-! # Evaluation -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.Evaluation

/-! Actual finite adelic function values of the Schwartz restricted tensor
product. These evaluation maps are linear, and on pure tensors they are
the finite product of the concrete local function values. -/

open scoped _root_.NumberField
open Filter

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def localEvaluation (x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (v : FiniteSchwartz.FinitePlace F) :
    Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N →ₗ[ℂ] ℂ where
  toFun f := f.val (fun i => x i v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vacuum_evaluation_eventually_one (x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∀ᶠ v : FiniteSchwartz.FinitePlace F in cofinite,
      localEvaluation F N x v (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = 1 := by
  have hx : ∀ᶠ v : FiniteSchwartz.FinitePlace F in cofinite,
      ∀ i, x i v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => (x i).property
  filter_upwards [hx] with v hv
  change LocallyConstant.charFn ℂ (Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v) (fun i => x i v) = 1
  apply (LocallyConstant.charFn_eq_one ℂ _ (Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v)).mpr
  exact fun i _ => hv i

def finiteSchwartzFunction : FiniteSchwartz.finiteSchwartz F N →ₗ[ℂ] ((Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ) :=
  LinearMap.pi fun x => TensorProjective.Evaluation.evaluate
    (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (localEvaluation F N x) (vacuum_evaluation_eventually_one F N x)

theorem finiteSchwartzFunction_pure
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    finiteSchwartzFunction F N (TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf) x =
      ∏ᶠ v, (f v).val (fun i => x i v) :=
  TensorProjective.Evaluation.evaluate_pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)
    (localEvaluation F N x) (vacuum_evaluation_eventually_one F N x) f hf

theorem vacuum_tensor_ne_zero :
    TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)
      (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (Filter.Eventually.of_forall fun _ => rfl) ≠ 0 := by
  intro h
  have he := congrArg (fun f => finiteSchwartzFunction F N f 0) h
  rw [finiteSchwartzFunction_pure, map_zero] at he
  change (∏ᶠ v : FiniteSchwartz.FinitePlace F, (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val 0) = 0 at he
  simp only [Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum_zero, finprod_one] at he
  exact one_ne_zero he

end RepresentationTheory.Theta.Adelic.Evaluation

namespace RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy

/-! Local constancy of the actual finite-product functions on finite adelic
positions. The restricted-product integrality condition is used explicitly. -/

open Filter Function
open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def integralOutside (s : Finset (FiniteSchwartz.FinitePlace F)) : Set (Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  {x | ∀ v, v ∉ s → ∀ i, x i v ∈ v.adicCompletionIntegers F}

theorem integralOutside_clopen (s : Finset (FiniteSchwartz.FinitePlace F)) :
    IsClopen (integralOutside F N s) := by
  constructor
  · change IsClosed {x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F |
      ∀ v, v ∉ s → ∀ i, x i v ∈ v.adicCompletionIntegers F}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro _
    apply isClosed_iInter
    intro i
    exact (Valued.isClosed_integer _).preimage
      ((RestrictedProduct.continuous_eval v).comp (continuous_apply i))
  · have hv : IsOpen {x : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F |
        ∀ v, v ∉ s → x v ∈ v.adicCompletionIntegers F} :=
      RestrictedProduct.isOpen_forall_imp_mem
        (A := fun v : FiniteSchwartz.FinitePlace F => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        (fun v : FiniteSchwartz.FinitePlace F => Valued.isOpen_integer (v.adicCompletion F))
        (p := fun v => v ∉ s)
    have hi (i : Fin N) : IsOpen {x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F |
        ∀ v, v ∉ s → x i v ∈ v.adicCompletionIntegers F} :=
      hv.preimage (show Continuous (fun x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => x i) from continuous_apply i)
    have h := isOpen_iInter_of_finite hi
    convert h using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, integralOutside]
    exact ⟨fun h i v hv => h v hv i, fun h v hv i => h i v hv⟩

theorem positionEvaluation_continuous (v : FiniteSchwartz.FinitePlace F) :
    Continuous (fun x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => fun i => x i v) :=
  continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)

theorem localFunction_locallyConstant
    (v : FiniteSchwartz.FinitePlace F) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N) :
    IsLocallyConstant (fun x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => f.val (fun i => x i v)) :=
  (Weil.UnitarySplitting.UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property).1.comp_continuous
    (positionEvaluation_continuous F N v)

theorem pure_product_decomposition
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (s : Finset (FiniteSchwartz.FinitePlace F)) (hs : ∀ v, v ∉ s → f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (∏ᶠ v, (f v).val (fun i => x i v)) =
      LocallyConstant.charFn ℂ (integralOutside_clopen F N s) x *
        ∏ v ∈ s, (f v).val (fun i => x i v) := by
  by_cases hx : x ∈ integralOutside F N s
  · rw [(LocallyConstant.charFn_eq_one ℂ x _).mpr hx, one_mul]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvs
    apply hv
    change (f v).val (fun i => x i v) = 1
    rw [hs v hvs]
    apply (LocallyConstant.charFn_eq_one ℂ _ (Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v)).mpr
    exact fun i _ => hx v hvs i
  · rw [(LocallyConstant.charFn_eq_zero ℂ x _).mpr hx, zero_mul]
    change ¬ (∀ v, v ∉ s → ∀ i, x i v ∈ v.adicCompletionIntegers F) at hx
    push Not at hx
    obtain ⟨v, hvs, i, hi⟩ := hx
    apply finprod_eq_zero _ v
    · rw [hs v hvs]
      apply (LocallyConstant.charFn_eq_zero ℂ _ (Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v)).mpr
      exact fun h => hi (h i (Set.mem_univ i))
    · exact TensorProjective.Evaluation.evaluation_finite_support
        (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (localEvaluation F N x)
        (vacuum_evaluation_eventually_one F N x) f hf

theorem pure_product_locallyConstant
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    IsLocallyConstant (fun x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F =>
      ∏ᶠ v, (f v).val (fun i => x i v)) := by
  have hbad : {v | f v ≠ Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v}.Finite := hf
  let s := hbad.toFinset
  have hs : ∀ v, v ∉ s → f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
    intro v hv
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
  have hp : IsLocallyConstant (fun x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F =>
      ∏ v ∈ s, (f v).val (fun i => x i v)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, Function.const_def] using (IsLocallyConstant.const (1 : ℂ))
    | @insert v s hv ih =>
      simp only [Finset.prod_insert hv]
      exact (localFunction_locallyConstant F N v (f v)).mul ih
  convert (LocallyConstant.charFn ℂ (integralOutside_clopen F N s)).isLocallyConstant.mul hp using 1
  funext x
  exact pure_product_decomposition F N f hf s hs x

end RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy

end

end OAI
