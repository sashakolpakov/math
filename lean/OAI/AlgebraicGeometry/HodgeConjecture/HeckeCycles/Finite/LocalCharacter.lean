import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal

/-! # Local Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LocalCharacter.CM

noncomputable section

/-! The actual local components of the constructed finite adelic
character. Every local component has exactly the integer ring as kernel. -/

open scoped Classical RestrictedProduct
open Filter

def singleMap (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : v.adicCompletion ℚ →+ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf where
  toFun := RestrictedProduct.single (fun w : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace => w.adicCompletionIntegers ℚ) v
  map_zero' := RestrictedProduct.single_zero _ v
  map_add' := RestrictedProduct.single_add _ v

theorem singleMap_same (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (x : v.adicCompletion ℚ) : singleMap v x v = x :=
  RestrictedProduct.single_eq_same _ _ _

theorem singleMap_other (v w : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (h : w ≠ v) (x : v.adicCompletion ℚ) :
    singleMap v x w = 0 := RestrictedProduct.single_eq_of_ne _ x h

theorem singleMap_continuous (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Continuous (singleMap v) := by
  let f : v.adicCompletion ℚ → RestrictedProduct (fun w : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace => w.adicCompletion ℚ)
      (fun w => (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)))
      (Filter.principal {w | w ≠ v}) := fun a =>
    ⟨Pi.single v a, by
      rw [Filter.eventually_principal]
      intro w hw
      simp [Pi.single_eq_of_ne hw]⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    exact continuous_single v
  have hco : cofinite ≤ Filter.principal {w : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace | w ≠ v} := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    simp
  exact (RestrictedProduct.continuous_inclusion hco).comp hf

def character (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : AddChar (v.adicCompletion ℚ) ℂ :=
  Constructed.AdelicCharacter.CM.Finite.character.compAddMonoidHom (singleMap v)

theorem character_apply (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (x : v.adicCompletion ℚ) :
    character v x = Constructed.AdelicCharacter.CM.Finite.character (singleMap v x) := rfl

theorem character_continuous (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Continuous (character v) :=
  Constructed.AdelicCharacter.CM.Finite.character_continuous.comp (singleMap_continuous v)

theorem character_unitary (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (x : v.adicCompletion ℚ) :
    ‖character v x‖ = 1 := Constructed.AdelicCharacter.CM.Finite.character_unitary _

theorem character_eq_one_iff (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (x : v.adicCompletion ℚ) :
    character v x = 1 ↔ x ∈ v.adicCompletionIntegers ℚ := by
  rw [character_apply, Constructed.AdelicCharacter.CM.Finite.character_eq_one_iff]
  constructor
  · intro h
    simpa only [singleMap_same] using h v
  · intro hx w
    by_cases hw : w = v
    · subst w
      simpa only [singleMap_same] using hx
    · rw [singleMap_other v w hw]
      exact (w.adicCompletionIntegers ℚ).zero_mem

theorem character_nontrivial (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    ∃ x : v.adicCompletion ℚ, character v x ≠ 1 := by
  obtain ⟨q, hq⟩ := v.valuation_surjective ℚ (WithZero.exp 1)
  refine ⟨algebraMap ℚ (v.adicCompletion ℚ) q, ?_⟩
  rw [ne_eq, character_eq_one_iff]
  change ¬ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1
  simp only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hq]
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LocalCharacter.CM
