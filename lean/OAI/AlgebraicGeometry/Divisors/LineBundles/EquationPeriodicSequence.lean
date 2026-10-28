import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationPeriodicComplex
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Submodule
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FiniteLength

/-! # Equation Periodic Sequence -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.EquationPeriodicSequence.BundleCycles

noncomputable section

/-!
# LineBundleCycles: scalar periodic complexes on actual module sequences

Linearity supplies the chain-map compatibility for every module map.
An actual short exact module sequence therefore induces a short exact
sequence of scalar periodic complexes.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R] {A M B : Type v}
    [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
    [AddCommGroup B] [Module R B]

def equationPeriodicMap (a b : R) (hM : ∀ m : M, (a * b) • m = 0)
    (hB : ∀ m : B, (a * b) • m = 0) (f : M →ₗ[R] B) :
    EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hM ⟶ EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b hB :=
  Periodic.Submodule.BundleCycles.endomorphismPeriodicMap _ _ _ _ _ _ _ _ f
    (by apply LinearMap.ext; intro m; exact (f.map_smul a m).symm)
    (by apply LinearMap.ext; intro m; exact (f.map_smul b m).symm)

def equationPeriodicSequence (a b : R)
    (hA : ∀ m : A, (a * b) • m = 0) (hM : ∀ m : M, (a * b) • m = 0)
    (hB : ∀ m : B, (a * b) • m = 0)
    (f : A →ₗ[R] M) (g : M →ₗ[R] B) (hfg : g.comp f = 0) :
    ShortComplex (HomologicalComplex (ModuleCat R) Periodic.PeriodicComplex.BundleCycles.periodicComplexShape) :=
  ShortComplex.mk (equationPeriodicMap a b hA hM f) (equationPeriodicMap a b hM hB g) (by
    apply HomologicalComplex.hom_ext
    intro i
    exact ModuleCat.hom_ext hfg)

theorem equationPeriodicSequence_shortExact (a b : R)
    (hA : ∀ m : A, (a * b) • m = 0) (hM : ∀ m : M, (a * b) • m = 0)
    (hB : ∀ m : B, (a * b) • m = 0)
    (f : A →ₗ[R] M) (g : M →ₗ[R] B) (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (equationPeriodicSequence a b hA hM hB f g hfg.linearMap_comp_eq_zero).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact ModuleCat.shortComplex_shortExact _ hfg hf hg

theorem equationPeriodic_kill_submodule (a b : R) (hM : ∀ m : M, (a * b) • m = 0)
    (P : Submodule R M) : ∀ m : P, (a * b) • m = 0 :=
  fun m => Subtype.ext (hM m.1)

theorem equationPeriodic_kill_quotient (a b : R) (hM : ∀ m : M, (a * b) • m = 0)
    (P : Submodule R M) : ∀ m : M ⧸ P, (a * b) • m = 0 := by
  intro m
  obtain ⟨m, rfl⟩ := P.mkQ_surjective m
  exact (P.mkQ.map_smul (a * b) m).symm.trans ((congrArg P.mkQ (hM m)).trans P.mkQ.map_zero)

theorem equationPeriodic_homology_finite_of_module (a b : R) (h : ∀ m : M, (a * b) • m = 0)
    (hM : Module.length R M ≠ ⊤) (i : Bool) :
    Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h).homology i) ≠ ⊤ :=
  Periodic.FiniteLength.BundleCycles.endomorphismPeriodicComplex_homology_length_ne_top _ _ _ _ hM i

theorem equationPeriodicEuler_zero_of_module (a b : R) (h : ∀ m : M, (a * b) • m = 0)
    (hM : Module.length R M ≠ ⊤)
    (h₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h).homology false) ≠ ⊤)
    (h₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h).homology true) ≠ ⊤) :
    Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h) h₀ h₁ = 0 :=
  Periodic.FiniteLength.BundleCycles.endomorphismPeriodicEulerLength_zero_of_finite _ _ _ _ h₀ h₁ hM

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.EquationPeriodicSequence.BundleCycles
