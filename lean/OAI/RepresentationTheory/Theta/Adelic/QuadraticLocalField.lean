import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

/-! # Quadratic Local Field -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField

noncomputable section

/-! An actual normed-field realization of a nonsplit quadratic algebra.
The spectral norm is used on a type copy; its topology is compared with
the existing coefficient topology rather than replacing that topology. -/

open scoped Classical

def FieldModel (k : Type) [Field k] (d : k) (_hns : ¬ IsSquare d) : Type := Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d

section Algebra
variable (k : Type) [Field k] (d : k) (hns : ¬ IsSquare d)

instance modelField : Field (FieldModel k d hns) := by
  let : Fact (∀ r : k, r ^ 2 ≠ d + 0 * r) := ⟨by
    intro r hr
    apply hns
    exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using hr.symm⟩⟩
  exact inferInstanceAs (Field (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

instance modelAlgebra : Algebra k (FieldModel k d hns) :=
  inferInstanceAs (Algebra k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

def algebraEquiv : FieldModel k d hns ≃ₐ[k] Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d := AlgEquiv.refl

instance modelFinite : FiniteDimensional k (FieldModel k d hns) :=
  inferInstanceAs (FiniteDimensional k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

theorem model_finrank : Module.finrank k (FieldModel k d hns) = 2 :=
  QuadraticAlgebra.finrank_eq_two d 0

def modelBasis : Module.Basis (Fin 2) k (FieldModel k d hns) :=
  (QuadraticAlgebra.basis d 0).map (algebraEquiv k d hns).symm.toLinearEquiv

def quadraticConjugation : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d ≃ₐ[k] Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d where
  __ := (starRingAut : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d ≃+* Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)
  commutes' a := by
    change star (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) a) = algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) a
    ext <;> simp

def conjugation : FieldModel k d hns ≃ₐ[k] FieldModel k d hns :=
  (algebraEquiv k d hns).trans ((quadraticConjugation k d).trans (algebraEquiv k d hns).symm)

theorem conjugation_nontrivial [CharZero k] :
    ∃ x : FieldModel k d hns, conjugation k d hns x ≠ x := by
  refine ⟨(algebraEquiv k d hns).symm ⟨0, 1⟩, ?_⟩
  intro h
  have hi := congrArg (fun x => ((algebraEquiv k d hns) x).im) h
  change -(1 : k) = 1 at hi
  norm_num at hi

theorem model_norm (x : FieldModel k d hns) :
    Algebra.norm k x = QuadraticAlgebra.norm (algebraEquiv k d hns x) := by
  rw [← Algebra.norm_eq_of_algEquiv (algebraEquiv k d hns)]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm _

end Algebra

variable (k : Type) [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
variable (d : k) (hns : ¬ IsSquare d)

instance modelNormedField : NontriviallyNormedField (FieldModel k d hns) :=
  spectralNorm.nontriviallyNormedField k (FieldModel k d hns)

instance modelNormedAlgebra : NormedAlgebra k (FieldModel k d hns) :=
  spectralNorm.normedAlgebra k (FieldModel k d hns)

instance modelComplete : CompleteSpace (FieldModel k d hns) :=
  FiniteDimensional.complete k (FieldModel k d hns)

def coordinates : FieldModel k d hns ≃L[k] (Fin 2 → k) :=
  (modelBasis k d hns).equivFun.toContinuousLinearEquiv

theorem coordinates_apply (x : FieldModel k d hns) :
    coordinates k d hns x = ![(algebraEquiv k d hns x).re, (algebraEquiv k d hns x).im] := rfl

instance modelLocallyCompact [LocallyCompactSpace k] : LocallyCompactSpace (FieldModel k d hns) :=
  (coordinates k d hns).toHomeomorph.isClosedEmbedding.locallyCompactSpace

instance modelMeasurable : MeasurableSpace (FieldModel k d hns) := borel _
instance modelBorel : BorelSpace (FieldModel k d hns) := ⟨rfl⟩

theorem model_nondiscrete : ¬ DiscreteTopology (FieldModel k d hns) := by
  intro h
  let : DiscreteTopology (FieldModel k d hns) := h
  exact not_isOpen_singleton (0 : FieldModel k d hns) (isOpen_discrete _)

def coefficientHomeomorph : FieldModel k d hns ≃ₜ Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d where
  toEquiv := (algebraEquiv k d hns).toEquiv
  continuous_toFun := by
    rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
    exact ⟨(continuous_apply 0).comp (coordinates k d hns).continuous,
      (continuous_apply 1).comp (coordinates k d hns).continuous⟩
  continuous_invFun := by
    have hc : Continuous (fun x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d => ![x.re, x.im]) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d
      · exact Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d
    have he : (fun x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d => (algebraEquiv k d hns).symm x) =
        (fun x => (coordinates k d hns).symm ![x.re, x.im]) := by
      funext x
      apply (coordinates k d hns).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, coordinates_apply, AlgEquiv.apply_symm_apply]
    change Continuous (fun x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d => (algebraEquiv k d hns).symm x)
    rw [he]
    exact (coordinates k d hns).symm.continuous.comp hc

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField
