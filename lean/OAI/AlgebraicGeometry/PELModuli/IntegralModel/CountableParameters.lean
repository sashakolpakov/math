import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CountableAlgebra
import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Cardinality

/-! # Countable Parameters -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CountableParameters

noncomputable section

/-!
Scheme-theoretic isolation from countably many points over an uncountable
algebraically closed field. Applied to an arithmetic parameter scheme, this
constructs a number-field parameter point. Countability must subsequently
be established for the particular Albanese parameter scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

abbrev ParameterPoints (X : Over (Spec (.of k))) :=
  Over.mk (𝟙 (Spec (.of k))) ⟶ X

def parameterPointClosedEquiv (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    ParameterPoints X ≃ closedPoints X.left where
  toFun p := pointEquivClosedPoint X.hom ⟨p.left, p.w⟩
  invFun q := Over.homMk ((pointEquivClosedPoint X.hom).symm q).val
    ((pointEquivClosedPoint X.hom).symm q).property
  left_inv p := by
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val ((pointEquivClosedPoint X.hom).symm_apply_apply ⟨p.left, p.w⟩)
  right_inv q := (pointEquivClosedPoint X.hom).apply_symm_apply q

def maximalClosedPoint (R : Type u) [CommRing R] (p : MaximalSpectrum R) :
    closedPoints (Spec (.of R)) :=
  ⟨⟨p.asIdeal, p.isMaximal.isPrime⟩,
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr p.isMaximal⟩

theorem maximalClosedPoint_injective (R : Type u) [CommRing R] :
    Function.Injective (maximalClosedPoint R) := by
  intro p q h
  exact MaximalSpectrum.ext (congrArg (fun x ↦ x.val.asIdeal) h)

theorem affine_discrete_of_countable_points [Uncountable k]
    (R : CommRingCat.{u}) (φ : CommRingCat.of k ⟶ R)
    [LocallyOfFiniteType (Spec.map φ)]
    [Countable (ParameterPoints (Over.mk (Spec.map φ)))] :
    DiscreteTopology (Spec R) := by
  have : LocallyOfFiniteType (Over.mk (Spec.map φ)).hom :=
    inferInstanceAs (LocallyOfFiniteType (Spec.map φ))
  have : Countable (closedPoints (Spec R)) :=
    (parameterPointClosedEquiv (Over.mk (Spec.map φ))).surjective.countable
  have : Countable (MaximalSpectrum R) := (maximalClosedPoint_injective R).countable
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    infer_instance
  · let := hR
    let : Algebra k R := φ.hom.toAlgebra
    have : Algebra.FiniteType k R :=
      RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp
        (inferInstance : LocallyOfFiniteType (Spec.map φ)))
    have : Module.Finite k R := CountableAlgebra.finite_of_countable_maximalSpectrum k R
    have : IsArtinianRing R := IsArtinianRing.of_finite k R
    exact (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero (R := R)).mpr
      ⟨inferInstance, inferInstance⟩

/-- A locally finite-type scheme over an uncountable algebraically closed
field cannot have a positive-dimensional part with only countably many
rational points. The conclusion is its actual discrete Zariski topology. -/
theorem discrete_of_countable_parameter_points [Uncountable k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [Countable (ParameterPoints X)] : DiscreteTopology X.left := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  obtain ⟨R, i, hi, y, hy⟩ := Scheme.exists_Spec_apply_eq x
  let : IsOpenImmersion i := hi
  let Z : Over (Spec (.of k)) := Over.mk (i ≫ X.hom)
  let j : Z ⟶ X := Over.homMk i rfl
  have : Mono j := Over.mono_of_mono_left j
  have hc : Countable (ParameterPoints Z) :=
    (show Function.Injective (fun p : ParameterPoints Z ↦ p ≫ j) from
      fun _ _ h ↦ (cancel_mono j).mp h).countable
  let φ := Spec.preimage (i ≫ X.hom)
  have hφ : Spec.map φ = i ≫ X.hom := Spec.map_preimage _
  have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  have : Countable (ParameterPoints (Over.mk (Spec.map φ))) := by rw [hφ]; exact hc
  have : DiscreteTopology (Spec R) := affine_discrete_of_countable_points R φ
  have hopen := i.isOpenMap {y} (isOpen_discrete {y})
  simpa only [Set.image_singleton, hy] using hopen

/-- Arithmetic parameter points descend once countability of the actual
complex parameter points has been established. -/
theorem complex_parameter_descends_of_countable
    {X : Scheme} (f : X ⟶ Spec (.of ℚ)) [LocallyOfFiniteType f]
    (p : Spec (.of ℂ) ⟶ CategoryTheory.Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
    [Countable (ParameterPoints (Over.mk (CategoryTheory.Limits.pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))))] :
    ∃ (K : Subfield ℂ), NumberField K ∧
      ∃ pK : Spec (.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom K.subtype) ≫ pK =
          p ≫ CategoryTheory.Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) := by
  let XC : Over (Spec (.of ℂ)) := Over.mk (CategoryTheory.Limits.pullback.snd f
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have : LocallyOfFiniteType XC.hom := inferInstanceAs
    (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))))
  have : DiscreteTopology XC.left := discrete_of_countable_parameter_points XC
  have hp : IsOpen ({p (IsLocalRing.closedPoint ℂ)} : Set XC.left) := isOpen_discrete _
  exact ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints.Abelian.complex_point_descends_of_isolated_baseChange f p hp

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CountableParameters
