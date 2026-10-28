import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorKill

/-! # Factor Sequence -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorSequence.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual short exact sequence for the factor cone

Inclusion is the first coordinate. Projection is the second coordinate
in degree zero and its negative in degree one. Thus the quotient is
the scalar complex (bc,a), with its original positive differentials.
-/

open _root_.CategoryTheory

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0)

def factorConeInclusion : EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (a * b) c h ⟶ FactorKill.BundleCycles.periodicFactorCone a b c h where
  f _ := ModuleCat.ofHom (LinearMap.inl R M M)
  comm' := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change M at m
      apply Prod.ext
      · change (a * b) • m + b • (0 : M) = (a * b) • m
        module
      · change (-(b * c)) • (0 : M) = 0
        module
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change M at m
      apply Prod.ext
      · change c • m + (0 : M) = c • m
        module
      · change (-a) • (0 : M) = 0
        module
    · exact (hij rfl).elim

def factorConeQuotient : FactorKill.BundleCycles.periodicFactorCone a b c h ⟶
    EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (b * c) a
      (EquationPeriodicComplex.BundleCycles.equationPeriodic_kill_swap a (b * c) (FactorKill.BundleCycles.factorCone_kill_source a b c h)) where
  f i := match i with
    | false => ModuleCat.ofHom (LinearMap.snd R M M)
    | true => ModuleCat.ofHom (-LinearMap.snd R M M)
  comm' := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change (b * c) • m.2 = -((-(b * c)) • m.2)
      module
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change a • (-m.2) = (-a) • m.2
      module
    · exact (hij rfl).elim

def factorConeSequence :
    ShortComplex (HomologicalComplex (ModuleCat R) PeriodicComplex.BundleCycles.periodicComplexShape) :=
  ShortComplex.mk (factorConeInclusion a b c h) (factorConeQuotient a b c h) (by
    apply HomologicalComplex.hom_ext
    intro i
    cases i
    · rfl
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change -(0 : M) = 0
      module)

theorem factorConeSequence_shortExact : (factorConeSequence a b c h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  cases i
  · apply ModuleCat.shortComplex_shortExact
    · exact (Function.Exact.inl_snd : Function.Exact (LinearMap.inl R M M) (LinearMap.snd R M M))
    · exact (LinearMap.inl_injective : Function.Injective (LinearMap.inl R M M))
    · exact (LinearMap.snd_surjective : Function.Surjective (LinearMap.snd R M M))
  · apply ModuleCat.shortComplex_shortExact
    · intro m
      change -m.2 = 0 ↔ ∃ x : M, (x, 0) = m
      rw [neg_eq_zero]
      exact (Function.Exact.inl_snd :
        Function.Exact (LinearMap.inl R M M) (LinearMap.snd R M M)) m
    · exact (LinearMap.inl_injective : Function.Injective (LinearMap.inl R M M))
    · intro m
      refine ⟨(0, -m), ?_⟩
      exact neg_neg m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorSequence.BundleCycles
