import OAI.RepresentationTheory.Theta.Adelic.CompactSupport
import OAI.RepresentationTheory.Theta.Intrinsic

/-! # Intrinsic Schwartz -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic

noncomputable section

/-! Finite-Schwartz transports for the native theta construction.
Surjectivity is proved by compactly supported rational-coset expansions;
it does not assume that a Schwartz input already factors. -/

open scoped _root_.NumberField Classical BigOperators

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Intrinsic.OneFormsIntrinsic

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem evaluation_surjective : Function.Surjective (Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N) := by
  intro φ
  obtain ⟨M, hM, hperiod⟩ :=
    Weil.AdelicSplitting.FiniteLattices.Construction.finite_locallyConstant_lattice_period φ.val φ.property.1 φ.property.2
  let hMF : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨s, hs⟩ := Weil.AdelicSplitting.FiniteCosets.Construction.finite_function_coset_expansion φ.val φ.property.2 (M : F) hMF hperiod
  let a (c : Weil.AdelicSplitting.FiniteCosets.Construction.FinitePositionQuotient (ι := Fin N) (M : F) hMF) :=
    Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionQuotientRep (M : F) hMF c)
  refine ⟨∑ c ∈ s, φ.val (a c) • Intrinsic.OneFormsIntrinsic.cosetInput F N (M : F) hMF (a c), ?_⟩
  apply Subtype.ext
  funext x
  change Adelic.Evaluation.finiteSchwartzFunction F N (∑ c ∈ s, φ.val (a c) • Intrinsic.OneFormsIntrinsic.cosetInput F N (M : F) hMF (a c)) x = _
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, Intrinsic.OneFormsIntrinsic.cosetInput_value]
  exact (hs x).symm

def liftFunction (φ : Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) : Adelic.FiniteSchwartz.finiteSchwartz F N :=
  (evaluation_surjective F N φ).choose

theorem liftFunction_value (φ : Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) (x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    Adelic.Evaluation.finiteSchwartzFunction F N (liftFunction F N φ) x = φ.val x :=
  congrArg (fun f : Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N => f.val x)
    (evaluation_surjective F N φ).choose_spec

def splitPositions {R : Type*} [TopologicalSpace R] (n m : ℕ) :
    (Fin (n + m) → R) ≃ₜ ((Fin n → R) × (Fin m → R)) :=
  (Homeomorph.piCongrLeft (Y := fun _ : Fin (n + m) => R) finSumFinEquiv).symm.trans
    Homeomorph.sumArrowHomeomorphProdArrow

theorem splitPositions_left {R : Type*} [TopologicalSpace R] (n m : ℕ)
    (x : Fin (n + m) → R) (i : Fin n) :
    (splitPositions n m x).1 i = x (Fin.castAdd m i) := rfl

theorem splitPositions_right {R : Type*} [TopologicalSpace R] (n m : ℕ)
    (x : Fin (n + m) → R) (i : Fin m) :
    (splitPositions n m x).2 i = x (Fin.natAdd n i) := rfl

def productFunction (n m : ℕ)
    (φ : Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F n) (ψ : Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F m) :
    Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F (n + m) := by
  let f : (Fin n → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) × (Fin m → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ :=
    fun x => φ.val x.1 * ψ.val x.2
  have hf : IsLocallyConstant f :=
    (φ.property.1.comp_continuous continuous_fst).mul
      (ψ.property.1.comp_continuous continuous_snd)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact (φ.property.2.prod ψ.property.2)
    intro x hx
    exact ⟨subset_tsupport _ (mul_ne_zero_iff.mp hx).1,
      subset_tsupport _ (mul_ne_zero_iff.mp hx).2⟩
  exact ⟨f ∘ splitPositions n m, hf.comp_continuous (splitPositions n m).continuous,
    hc.comp_homeomorph (splitPositions n m)⟩

def productInput (n m : ℕ) (f : Adelic.FiniteSchwartz.finiteSchwartz F n) (g : Adelic.FiniteSchwartz.finiteSchwartz F m) :
    Adelic.FiniteSchwartz.finiteSchwartz F (n + m) :=
  liftFunction F (n + m) (productFunction F n m (Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F n f) (Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F m g))

theorem productInput_value (n m : ℕ) (f : Adelic.FiniteSchwartz.finiteSchwartz F n) (g : Adelic.FiniteSchwartz.finiteSchwartz F m)
    (x : Fin (n + m) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    Adelic.Evaluation.finiteSchwartzFunction F (n + m) (productInput F n m f g) x =
      Adelic.Evaluation.finiteSchwartzFunction F n f (fun i => x (Fin.castAdd m i)) *
      Adelic.Evaluation.finiteSchwartzFunction F m g (fun j => x (Fin.natAdd n j)) := by
  rw [productInput, liftFunction_value]
  rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic
