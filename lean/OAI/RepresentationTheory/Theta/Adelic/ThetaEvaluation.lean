import OAI.RepresentationTheory.Theta.Adelic.CompactSupport
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest

/-! # Theta Evaluation -/

namespace OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

noncomputable section

/-! The convergent adelic theta functional on the actual finite Schwartz
tensor space. Pure tensors agree with AdelicSplitting's restricted test families. -/

open scoped _root_.NumberField
open Filter

open OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest.Construction
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

abbrev ArchimedeanTests :=
  ∀ v : NumberField.InfinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) N

def testFamily (φ : ArchimedeanTests F N)
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N where
  component v := match v with
    | .inl v => φ v
    | .inr v => f v
  unramified := hf

def archimedeanValue (φ : ArchimedeanTests F N) (q : Fin N → F) : ℂ :=
  ∏ v : NumberField.InfinitePlace F,
    (φ v).val (fun i => Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl v) (q i))

def summand (φ : ArchimedeanTests F N) :
    FiniteSchwartz.finiteSchwartz F N →ₗ[ℂ] ((Fin N → F) → ℂ) where
  toFun f q := archimedeanValue F N φ q *
    Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q)
  map_add' f g := by
    funext q
    simp only [map_add, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext q
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem finite_value_pure (φ : ArchimedeanTests F N)
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    Evaluation.finiteSchwartzFunction F N (TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf) x =
      (testFamily F N φ f hf).finiteValue F N x := by
  rw [Evaluation.finiteSchwartzFunction_pure]
  symm
  change (∏' v : FiniteSchwartz.FinitePlace F, (f v).val (fun i => x i v)) =
    ∏ᶠ v : FiniteSchwartz.FinitePlace F, (f v).val (fun i => x i v)
  apply tprod_eq_finprod
  exact eventually_cofinite.mp ((testFamily F N φ f hf).finite_localValue_eventually_one F N x)

theorem summand_pure (φ : ArchimedeanTests F N)
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) (q : Fin N → F) :
    summand F N φ (TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf) q =
      (testFamily F N φ f hf).value F N (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) (q i)) := by
  change archimedeanValue F N φ q * _ = _
  rw [finite_value_pure F N φ, Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily.value_factorization]
  rfl

def fullSummand (φ : ArchimedeanTests F N) :
    (PiTensorProduct ℂ (fun v : FiniteSchwartz.FinitePlace F => Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)) →ₗ[ℂ]
      ((Fin N → F) → ℂ) :=
  LinearMap.pi fun q => archimedeanValue F N φ q •
    PiTensorProduct.lift (TensorProjective.Evaluation.evaluationMultilinear (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)
      (Evaluation.localEvaluation F N (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q))
      (Evaluation.vacuum_evaluation_eventually_one F N (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q)))

theorem summand_summable (φ : ArchimedeanTests F N) (f : FiniteSchwartz.finiteSchwartz F N) :
    Summable (summand F N φ f) := by
  have hfull (g : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
      (hg : ∀ᶠ v in cofinite, g v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
      fullSummand F N φ (PiTensorProduct.tprod ℂ g) =
        fun q => (testFamily F N φ g hg).value F N
          (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) (q i)) := by
    funext q
    exact summand_pure F N φ g hg q
  have hall : ∀ x, x ∈ TensorProjective.Restricted.restrictedTensor (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) →
      Summable (fullSummand F N φ x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [hfull g hg]
      exact (testFamily F N φ g hg).theta_summable F N
    | zero =>
      rw [map_zero]
      exact summable_zero
    | add x y _ _ hxs hys =>
      rw [map_add]
      exact hxs.add hys
    | smul c x _ hxs =>
      rw [map_smul]
      exact Summable.const_smul c hxs
  exact hall f.val f.property

def theta (φ : ArchimedeanTests F N) : FiniteSchwartz.finiteSchwartz F N →ₗ[ℂ] ℂ where
  toFun f := ∑' q, summand F N φ f q
  map_add' f g := by
    simp only [map_add, Pi.add_apply]
    exact (summand_summable F N φ f).tsum_add (summand_summable F N φ g)
  map_smul' c f := by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    exact Summable.tsum_const_smul c (summand_summable F N φ f)

theorem theta_pure (φ : ArchimedeanTests F N)
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    ThetaEvaluation.theta F N φ (TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf) = (testFamily F N φ f hf).theta F N := by
  unfold ThetaEvaluation.theta Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily.theta
  exact tsum_congr (summand_pure F N φ f hf)

end

end OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
