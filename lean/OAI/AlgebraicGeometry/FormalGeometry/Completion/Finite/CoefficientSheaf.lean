import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientTopology
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Coefficient Sheaf -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction

noncomputable section

/-!
# Completion: the finite-coefficient exact sequence on the actual pro-étale site

The continuous-function coefficient sheaves fit into the exact sequence
ℤ_ℓ --ℓⁿ--> ℤ_ℓ --> ℤ/ℓⁿ. Exactness is proved on sections, including
continuity of the quotient function in the kernel.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) [Fact ℓ.Prime]

/-- Reduction of continuous integral coefficient functions. -/
def continuousCoefficientReduction :
    continuousMapPresheafAb (ℤ_[ℓ]) ⟶ continuousMapPresheafAb (ZMod (ℓ ^ n)) where
  app U := AddCommGrpCat.ofHom {
    toFun f := ⟨fun x => PadicInt.toZModPow n (f x),
      (CoefficientTopology.Construction.continuous_padicInt_toZModPow ℓ n).comp f.continuous⟩
    map_zero' := by
      apply ContinuousMap.ext
      intro x
      exact map_zero (PadicInt.toZModPow n)
    map_add' f g := by
      apply ContinuousMap.ext
      intro x
      exact map_add (PadicInt.toZModPow n) (f x) (g x) }
  naturality := by intros; rfl

/-- Finite coefficients on the actual pro-étale site, in the cohomology universe. -/
def finiteEllAdicCoefficient (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj
    (((Scheme.ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _
      Scheme.proetaleTopology).obj
        ⟨continuousMapPresheafAb (ZMod (ℓ ^ n)),
          .of_le Scheme.proetaleTopology_le_fpqcTopology
            (isSheaf_fpqcTopology_continuousMapPresheafAb _)⟩)

/-- Reduction on the actual coefficient sheaves. -/
def finiteEllAdicReduction (X : Scheme.{u}) :
    ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X ⟶ finiteEllAdicCoefficient ℓ n X where
  hom := Functor.whiskerRight
    (Functor.whiskerLeft (Scheme.ProEt.forget X ⋙ Over.forget _).op
      (continuousCoefficientReduction ℓ n)) AddCommGrpCat.uliftFunctor

variable (X : Scheme.{u})

theorem finiteEllAdicReduction_comp_scalar :
    Cohomology.Construction.liftedEllAdicScalar ℓ X ((ℓ : ℤ_[ℓ]) ^ n) ≫ finiteEllAdicReduction ℓ n X = 0 := by
  ext U f
  change ULift.{u + 1} C(U.unop.left, ℤ_[ℓ]) at f
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  change PadicInt.toZModPow n ((ℓ : ℤ_[ℓ]) ^ n * f.down t) = 0
  simp [← Nat.cast_pow]

/-- The finite-coefficient short complex. -/
def finiteEllAdicShortComplex : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  ShortComplex.mk (Cohomology.Construction.liftedEllAdicScalar ℓ X ((ℓ : ℤ_[ℓ]) ^ n))
    (finiteEllAdicReduction ℓ n X) (finiteEllAdicReduction_comp_scalar ℓ n X)

theorem finiteEllAdicReduction_app_surjective (U : X.ProEtᵒᵖ) :
    Function.Surjective ((finiteEllAdicReduction ℓ n X).hom.app U) := by
  intro f
  change ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) at f
  have hc : Continuous (fun a : ZMod (ℓ ^ n) => (a.val : ℤ_[ℓ])) :=
    continuous_of_discreteTopology
  let g : C(U.unop.left, ℤ_[ℓ]) :=
    ⟨fun t => ((f.down t).val : ℤ_[ℓ]), hc.comp f.down.continuous⟩
  refine ⟨ULift.up g, ?_⟩
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  exact CoefficientTopology.Construction.padicInt_toZModPow_section ℓ n (f.down t)

theorem finiteEllAdicScalar_app_injective (U : X.ProEtᵒᵖ) :
    Function.Injective ((Cohomology.Construction.liftedEllAdicScalar ℓ X ((ℓ : ℤ_[ℓ]) ^ n)).hom.app U) := by
  intro f g h
  change ULift.{u + 1} C(U.unop.left, ℤ_[ℓ]) at f g
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  have ht := congrArg (fun a : ULift.{u + 1} C(U.unop.left, ℤ_[ℓ]) => a.down t) h
  change (ℓ : ℤ_[ℓ]) ^ n * f.down t = (ℓ : ℤ_[ℓ]) ^ n * g.down t at ht
  exact mul_left_cancel₀ (pow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)) ht

theorem finiteEllAdicShortComplex_app_exact (U : X.ProEtᵒᵖ) :
    ((finiteEllAdicShortComplex ℓ n X).map
      ((sheafToPresheaf _ Ab.{u + 1}) ⋙ (evaluation _ _).obj U)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro f hf
  change ULift.{u + 1} C(U.unop.left, ℤ_[ℓ]) at f
  have hf' : ∀ t, PadicInt.toZModPow n (f.down t) = 0 := by
    intro t
    exact congrArg (fun a : ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) => a.down t) hf
  obtain ⟨g, hg⟩ := CoefficientTopology.Construction.continuousMap_padicInt_divisible ℓ n f.down hf'
  refine ⟨ULift.up g, ?_⟩
  apply ULift.ext
  exact ContinuousMap.ext hg

instance finiteEllAdicReduction_epi : Epi (finiteEllAdicReduction ℓ n X) := by
  have h : Epi (finiteEllAdicReduction ℓ n X).hom :=
    (NatTrans.epi_iff_epi_app _).mpr fun U =>
      ConcreteCategory.epi_of_surjective _ (finiteEllAdicReduction_app_surjective ℓ n X U)
  exact (sheafToPresheaf _ Ab.{u + 1}).epi_of_epi_map h

instance finiteEllAdicScalar_mono : Mono (Cohomology.Construction.liftedEllAdicScalar ℓ X ((ℓ : ℤ_[ℓ]) ^ n)) := by
  have h : Mono (Cohomology.Construction.liftedEllAdicScalar ℓ X ((ℓ : ℤ_[ℓ]) ^ n)).hom :=
    (NatTrans.mono_iff_mono_app _).mpr fun U =>
      ConcreteCategory.mono_of_injective _ (finiteEllAdicScalar_app_injective ℓ n X U)
  exact (sheafToPresheaf _ Ab.{u + 1}).mono_of_mono_map h

/-- The scalar/reduction sequence is short exact in actual pro-étale sheaves. -/
theorem finiteEllAdicShortComplex_shortExact : (finiteEllAdicShortComplex ℓ n X).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ (finiteEllAdicScalar_mono ℓ n X)
    (finiteEllAdicReduction_epi ℓ n X)
  let S := finiteEllAdicShortComplex ℓ n X
  apply ShortComplex.exact_of_f_is_kernel
  apply isLimitOfReflects (sheafToPresheaf _ Ab.{u + 1})
  apply evaluationJointlyReflectsLimits
  intro U
  let E := (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⋙ (evaluation _ _).obj U
  change IsLimit (E.mapCone (KernelFork.ofι S.f S.zero))
  refine (KernelFork.isLimitMapConeEquiv (KernelFork.ofι S.f S.zero) E).symm ?_
  have : Mono (S.map E).f :=
    ConcreteCategory.mono_of_injective _ (finiteEllAdicScalar_app_injective ℓ n X U)
  exact (finiteEllAdicShortComplex_app_exact ℓ n X U).fIsKernel

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction
