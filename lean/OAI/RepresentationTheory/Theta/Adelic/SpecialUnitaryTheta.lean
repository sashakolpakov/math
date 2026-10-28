import OAI.RepresentationTheory.Theta.Adelic.ExactLevi
import OAI.RepresentationTheory.Theta.Adelic.RationalSU
import OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
import OAI.RepresentationTheory.Theta.Adelic.CongruenceLevel
import OAI.RepresentationTheory.Weil.AdelicSplitting.No

/-! # Special Unitary Theta -/

namespace OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

noncomputable section

/-! Exact theta covariance for the actual finite special-unitary action
and its archimedean companion. AdelicSplitting supplies rational compatibility from
normalized local data; compatibility and smoothness are not new premises. -/

open Filter
open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    MeasurableSpace v.Completion := borel v.Completion
local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    BorelSpace v.Completion := ⟨rfl⟩
local instance (F : Type) [Field F] [NumberField F] (v : FiniteSchwartz.FinitePlace F) :
    MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance (F : Type) [Field F] [NumberField F] (v : FiniteSchwartz.FinitePlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem linearMap_ext_pure
    {I : Type*} {S : I → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    (vac : ∀ i, S i) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T U : TensorProjective.Restricted.restrictedTensor vac →ₗ[ℂ] M)
    (h : ∀ f hf, T (TensorProjective.Restricted.pure vac f hf) = U (TensorProjective.Restricted.pure vac f hf)) : T = U := by
  have hall : ∀ x, ∀ hx : x ∈ TensorProjective.Restricted.restrictedTensor vac, T ⟨x, hx⟩ = U ⟨x, hx⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact h f hf
    | zero => exact (map_zero T).trans (map_zero U).symm
    | add x y hx hy hxs hys =>
      change T (⟨x, hx⟩ + ⟨y, hy⟩) = U (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, hxs, hys]
    | smul c x hx hxs =>
      change T (c • ⟨x, hx⟩) = U (c • ⟨x, hx⟩)
      rw [map_smul, map_smul, hxs]
  exact LinearMap.ext (fun x => hall x.val x.property)

variable (F : Type) [Field F] [NumberField F] {d : F} {n m : ℕ}
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

def archimedeanAction (g : RationalSU.ArchimedeanSU F H) (φ : ThetaEvaluation.ArchimedeanTests F (n * m)) :
    ThetaEvaluation.ArchimedeanTests F (n * m) := fun v =>
  Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) (n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl v))
    (FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) (g v)) (φ v)

theorem finiteAction_pure (g : FiniteSchwartz.FiniteSU F H)
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) (n * m))
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) :
    ∃ hf' : ∀ᶠ v in cofinite,
      FiniteSchwartz.localSUAction F H K hd C P D v (g v) (f v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v,
      FiniteSchwartz.finiteAction F H K hd C P D g (TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m)) f hf) =
        TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m)) (fun v => FiniteSchwartz.localSUAction F H K hd C P D v (g v) (f v)) hf' := by
  have hf' : ∀ᶠ v in cofinite,
      FiniteSchwartz.localSUAction F H K hd C P D v (g v) (f v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v := by
    filter_upwards [hf, g.property, FiniteSchwartz.localSUAction_unramified F H K hd C P D] with v hv hg hρ
    rw [hv]
    exact hρ (g v) hg
  refine ⟨hf', ?_⟩
  apply Subtype.ext
  exact TensorProjective.Restricted.fullAction_pure _ _ g f

theorem rational_testFamily_action (g : SpecialUnitary.SU H.val) (φ : ThetaEvaluation.ArchimedeanTests F (n * m))
    (f : ∀ v : FiniteSchwartz.FinitePlace F, Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) (n * m))
    (hf : ∀ᶠ v in cofinite, f v = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v)
    (hf' : ∀ᶠ v in cofinite,
      FiniteSchwartz.localSUAction F H K hd C P D v (RationalSU.rationalFiniteSU F H g v) (f v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) :
    (ThetaEvaluation.testFamily F (n * m) φ f hf).act F (n * m) C.ψ
      (Weil.AdelicSplitting.NormalizedRationalFamilies.Construction.normalizedRationalFamily F d hd n m H K C P D (SpecialUnitary.includeUnitary H.val g, 1)) =
      ThetaEvaluation.testFamily F (n * m)
        (archimedeanAction F H K hd C P D (RationalSU.rationalArchimedeanSU F H g) φ)
        (fun v => FiniteSchwartz.localSUAction F H K hd C P D v (RationalSU.rationalFiniteSU F H g v) (f v)) hf' := by
  apply Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily.ext
  intro v
  cases v with
  | inl v =>
    change Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _
      (D.atPlace (.inl v) (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val (.inl v) (SpecialUnitary.includeUnitary H.val g),
        Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F K.val (.inl v) 1)) (φ v) = _
    rw [map_one]
    rfl
  | inr v =>
    change Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _
      (D.atPlace (.inr v) (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val (.inr v) (SpecialUnitary.includeUnitary H.val g),
        Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F K.val (.inr v) 1)) (f v) = _
    rw [map_one]
    rfl

variable (hds : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)

include hds hH hK in
theorem normalizedRationalFamily_theta (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val)
    (f : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F (n * m)) :
    (f.act F (n * m) C.ψ (Weil.AdelicSplitting.NormalizedRationalFamilies.Construction.normalizedRationalFamily F d hd n m H K C P D g)).theta F (n * m) =
      f.theta F (n * m) := by
  obtain ⟨-, -, r, hr, -, hcompat⟩ :=
    Weil.AdelicSplitting.No.adelic_unitary_splitting_compatible_with_rational_points
      F d ⟨hd, hds⟩ n m H K hH hK C P D
  have hgraph : (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g,
      Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F (n * m) C.ψ (Weil.AdelicSplitting.NormalizedRationalFamilies.Construction.normalizedRationalFamily F d hd n m H K C P D g)) ∈
        Weil.AdelicSplitting.Rational.Construction.rationalGraph F (n * m) C.ψ := by
    apply (hr _ _).mpr
    exact (hcompat g).symm
  exact ExactLevi.RationalTheta.rational_theta F (n * m) C.ψ C.ψ_continuous C.ψ_unitary
    C.ψ_nontrivial C.ψ_principal _ _ hgraph f

include hds hH hK in
theorem rational_specialUnitary_theta (g : SpecialUnitary.SU H.val) (φ : ThetaEvaluation.ArchimedeanTests F (n * m))
    (f : FiniteSchwartz.finiteSchwartz F (n * m)) :
    ThetaEvaluation.theta F (n * m) (archimedeanAction F H K hd C P D (RationalSU.rationalArchimedeanSU F H g) φ)
      (FiniteSchwartz.finiteAction F H K hd C P D (RationalSU.rationalFiniteSU F H g) f) = ThetaEvaluation.theta F (n * m) φ f := by
  let T : FiniteSchwartz.finiteSchwartz F (n * m) →ₗ[ℂ] ℂ :=
    (ThetaEvaluation.theta F (n * m) (archimedeanAction F H K hd C P D (RationalSU.rationalArchimedeanSU F H g) φ)).comp
      (FiniteSchwartz.finiteAction F H K hd C P D (RationalSU.rationalFiniteSU F H g)).toLinearMap
  have he : T = ThetaEvaluation.theta F (n * m) φ := by
    apply linearMap_ext_pure
    intro f hf
    obtain ⟨hf', hact⟩ := finiteAction_pure F H K hd C P D (RationalSU.rationalFiniteSU F H g) f hf
    change ThetaEvaluation.theta F (n * m)
      (archimedeanAction F H K hd C P D (RationalSU.rationalArchimedeanSU F H g) φ)
        (FiniteSchwartz.finiteAction F H K hd C P D (RationalSU.rationalFiniteSU F H g) (TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m)) f hf)) = _
    rw [hact, ThetaEvaluation.theta_pure, ThetaEvaluation.theta_pure,
      ← rational_testFamily_action F H K hd C P D g φ f hf hf']
    exact normalizedRationalFamily_theta F H K hd C P D hds hH hK (SpecialUnitary.includeUnitary H.val g, 1) _
  exact DFunLike.congr_fun he f

include hds hH hK in
theorem finite_family_theta_level (hN : 0 < n * m)
    (Φ : Finset (FiniteSchwartz.finiteSchwartz F (n * m))) (K₀ : OpenSubgroup (FiniteSchwartz.FiniteSU F H)) :
    ∃ L : OpenSubgroup (FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
      ∀ f ∈ Φ, ∀ g : SpecialUnitary.SU H.val, RationalSU.rationalFiniteSU F H g ∈ L →
        ∀ φ : ThetaEvaluation.ArchimedeanTests F (n * m),
          ThetaEvaluation.theta F (n * m) (archimedeanAction F H K hd C P D (RationalSU.rationalArchimedeanSU F H g) φ) f =
            ThetaEvaluation.theta F (n * m) φ f := by
  obtain ⟨L, hLc, hLK, hfix⟩ := CongruenceLevel.finite_family_congruence_level
    F d hd n m hN H K C P D Φ K₀
  refine ⟨L, hLc, hLK, fun f hf g hg φ => ?_⟩
  have h := rational_specialUnitary_theta F H K hd C P D hds hH hK g φ f
  rwa [hfix f hf (RationalSU.rationalFiniteSU F H g) hg] at h

end

end OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta
