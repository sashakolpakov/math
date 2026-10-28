import OAI.RepresentationTheory.Theta.Adelic.Evaluation
import OAI.RepresentationTheory.Theta.Adelic.RestrictedBoxes

/-! # Compact Support -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.CompactSupport

/-! Compact support of finite adelic pure tensors, proved using compact
coordinate projections of local supports and the restricted-product topology. -/

open Filter Function
open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem vacuum_tsupport_subset (v : FiniteSchwartz.FinitePlace F) :
    tsupport (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val ⊆ Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice F N v := by
  apply closure_minimal _ (Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v).isClosed
  intro x hx
  by_contra h
  exact hx ((LocallyConstant.charFn_eq_zero ℂ x (Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_clopen F N v)).mpr h)

def coordinateSupport
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (i : Fin N) (v : FiniteSchwartz.FinitePlace F) : Set (v.adicCompletion F) :=
  (fun z => z i) '' tsupport (f v).val

theorem coordinateSupport_compact
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (i : Fin N) (v : FiniteSchwartz.FinitePlace F) : IsCompact (coordinateSupport F N f i v) :=
  (Weil.UnitarySplitting.UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp (f v).property).2.image (continuous_apply i)

theorem coordinateSupport_eventually_integral
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (i : Fin N) :
    ∀ᶠ v in cofinite, coordinateSupport F N f i v ⊆ v.adicCompletionIntegers F := by
  filter_upwards [hf] with v hv
  rintro x ⟨z, hz, rfl⟩
  rw [hv] at hz
  exact vacuum_tsupport_subset F N v hz i (Set.mem_univ i)

def adelicSupportBox
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N) :
    Set (Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  Set.univ.pi fun i => {x : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F | ∀ v, x v ∈ coordinateSupport F N f i v}

theorem adelicSupportBox_compact
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    IsCompact (adelicSupportBox F N f) := by
  simp only [adelicSupportBox, Set.pi, Set.mem_univ, forall_true_left]
  apply isCompact_pi_infinite
  intro i
  exact RestrictedBoxes.isCompact_box
    (fun v : FiniteSchwartz.FinitePlace F => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (coordinateSupport F N f i) (coordinateSupport_compact F N f i)
    (coordinateSupport_eventually_integral F N f hf i)

theorem pure_product_compactSupport
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    HasCompactSupport (fun x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F =>
      ∏ᶠ v, (f v).val (fun i => x i v)) := by
  apply HasCompactSupport.of_support_subset_isCompact (adelicSupportBox_compact F N f hf)
  intro x hx i _ v
  refine ⟨fun j => x j v, subset_tsupport _ ?_, rfl⟩
  intro hz
  exact hx (finprod_eq_zero _ v hz
    (TensorProjective.Evaluation.evaluation_finite_support
      (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (Evaluation.localEvaluation F N x)
      (Evaluation.vacuum_evaluation_eventually_one F N x) f hf))

end RepresentationTheory.Theta.Adelic.CompactSupport

namespace RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

/-! The restricted tensor evaluation lands in the space of actual locally
constant, compactly supported functions on finite adelic positions. -/

open Filter Function
open scoped _root_.NumberField TensorProduct

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy OAI.RepresentationTheory.Theta.Adelic.CompactSupport

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def adelicSchwartzFunctions : Submodule ℂ ((Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.zero, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.comp (fun z => c * z), hf.2.smul_left⟩

theorem adelicSchwartzFunctions_eq_span :
    adelicSchwartzFunctions F N = Submodule.span ℂ
      {f : (Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ | IsLocallyConstant f ∧ HasCompactSupport f} :=
  (Submodule.span_eq (adelicSchwartzFunctions F N)).symm

theorem finiteSchwartzFunction_mem (x : FiniteSchwartz.finiteSchwartz F N) :
    Evaluation.finiteSchwartzFunction F N x ∈ adelicSchwartzFunctions F N := by
  let T : (⨂[ℂ] v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N) →ₗ[ℂ]
      ((Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ) := LinearMap.pi fun z =>
    PiTensorProduct.lift (TensorProjective.Evaluation.evaluationMultilinear (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)
      (Evaluation.localEvaluation F N z) (Evaluation.vacuum_evaluation_eventually_one F N z))
  have ht (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
      (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
      T (PiTensorProduct.tprod ℂ f) = fun z => ∏ᶠ v, (f v).val (fun i => z i v) := by
    funext z
    change PiTensorProduct.lift (TensorProjective.Evaluation.evaluationMultilinear _ _ _)
      (PiTensorProduct.tprod ℂ f) = _
    rw [PiTensorProduct.lift.tprod]
    exact ite_eq_left hf
  have hall : ∀ y ∈ TensorProjective.Restricted.restrictedTensor (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N),
      T y ∈ adelicSchwartzFunctions F N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      rw [ht f hf]
      exact ⟨Evaluation.AdelicLocalConstancy.pure_product_locallyConstant F N f hf, pure_product_compactSupport F N f hf⟩
    | zero => simpa only [map_zero] using (adelicSchwartzFunctions F N).zero_mem
    | add y z _ _ hy hz =>
      simpa only [map_add] using (adelicSchwartzFunctions F N).add_mem hy hz
    | smul c y _ hy =>
      simpa only [map_smul] using (adelicSchwartzFunctions F N).smul_mem c hy
  exact hall x.val x.property

def toAdelicSchwartz : FiniteSchwartz.finiteSchwartz F N →ₗ[ℂ] adelicSchwartzFunctions F N :=
  (Evaluation.finiteSchwartzFunction F N).codRestrict _ (finiteSchwartzFunction_mem F N)

theorem toAdelicSchwartz_pure
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (z : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (toAdelicSchwartz F N (TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf)).val z =
      ∏ᶠ v, (f v).val (fun i => z i v) :=
  Evaluation.finiteSchwartzFunction_pure F N f hf z

end RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

end

end OAI
