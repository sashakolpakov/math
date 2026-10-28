import OAI.AlgebraicTopology.Duality.Poincare.RelativeCochainDual
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Relative Universal Coefficient -/

namespace OAI.AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient

noncomputable section

/-!
# Universal-coefficient evaluation for actual relative rational cochains

The first part proves the algebraic universal-coefficient theorem for a
cochain complex identified with the dual of a chain complex into an injective
coefficient field. The pairing is defined by descending actual evaluation
through the two cycle/boundary quotients. The second part applies the theorem
to the already constructed relative rational-cochain / integral-chain duality.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace InjectiveDuality
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R F : Type} [CommRing R] [Field F]
  [Module R F]

theorem functional_extends [Module.Injective R F] {V W : Type} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (f : V →ₗ[R] W) (hf : Function.Injective f)
    (g : V →ₗ[R] F) : ∃ h : W →ₗ[R] F, h.comp f = g := by
  exact Module.Injective.extension_property R F V W f hf g

theorem functional_factors [Module.Injective R F] {V W : Type} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (f : V →ₗ[R] W) (g : V →ₗ[R] F)
    (hg : ∀ v, f v = 0 → g v = 0) :
    ∃ h : W →ₗ[R] F, h.comp f = g := by
  let g₀ : LinearMap.range f →ₗ[R] F :=
    ((LinearMap.ker f).liftQ g hg).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨h, hh⟩ := functional_extends (LinearMap.range f).subtype Subtype.val_injective g₀
  refine ⟨h, ?_⟩
  ext v
  have hv := LinearMap.congr_fun hh ⟨f v, ⟨v, rfl⟩⟩
  change h (f v) = g₀ ⟨f v, ⟨v, rfl⟩⟩ at hv
  change h (f v) = g v
  rw [hv]
  simp [g₀]

variable [SMulCommClass R F F]

variable (C : ChainComplex (ModuleCat.{0} R) ℕ)
  (D : CochainComplex (ModuleCat.{0} F) ℕ)
  (e : ∀ n, D.X n ≃ₗ[F] (C.X n →ₗ[R] F))
  (he : ∀ i j (c : D.X i), e j (D.d i j c) = (e i c).comp (C.d j i).hom)

include he

theorem cocycle_boundary (n i : ℕ) (c : Cohomology.Singular.Representatives.cochainCocycles D n) (z : C.X i) :
    e n c.val (C.d i n z) = 0 := by
  have h := LinearMap.congr_fun (he n i c.val) z
  simpa only [Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero D n i c, map_zero,
    LinearMap.zero_apply, LinearMap.comp_apply] using h.symm

theorem coboundary_cycle (i n : ℕ) (c : D.X i) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    e n (D.d i n c) z.val = 0 := by
  have h := LinearMap.congr_fun (he i n c) z.val
  simpa only [LinearMap.comp_apply, Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero C n i z, map_zero] using h

def evaluateCocycle (n : ℕ) (c : Cohomology.Singular.Representatives.cochainCocycles D n) : C.homology n →ₗ[R] F :=
  ((Cohomology.Singular.ChainRepresentatives.chainBoundaries C n).liftQ ((e n c.val).comp (Cohomology.Singular.ChainRepresentatives.chainCycles C n).subtype)
    (by
      rintro z ⟨w, rfl⟩
      exact cocycle_boundary C D e he n _ c w)).comp
    (Cohomology.Singular.ChainRepresentatives.homologyQuotientIso C n).toLinearEquiv.toLinearMap

@[simp]
theorem evaluateCocycle_class (n : ℕ) (c : Cohomology.Singular.Representatives.cochainCocycles D n) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    evaluateCocycle C D e he n c (Cohomology.Singular.ChainRepresentatives.chainClass C n z) = e n c.val z.val := by
  dsimp only [evaluateCocycle, Cohomology.Singular.ChainRepresentatives.chainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

def cocycleEvaluation (n : ℕ) : Cohomology.Singular.Representatives.cochainCocycles D n →ₗ[F] (C.homology n →ₗ[R] F) where
  toFun := evaluateCocycle C D e he n
  map_add' c d := by
    ext h
    obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n h
    simp only [evaluateCocycle_class, LinearMap.add_apply, Submodule.coe_add,
      map_add]
  map_smul' r c := by
    ext h
    obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n h
    simp only [evaluateCocycle_class, LinearMap.smul_apply, Submodule.coe_smul,
      map_smul, RingHom.id_apply]

@[simp]
theorem cocycleEvaluation_boundary (n : ℕ) (c : (D.sc n).X₁) :
    cocycleEvaluation C D e he n (Cohomology.Singular.Representatives.cochainBoundaryMap D n c) = 0 := by
  ext h
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n h
  change evaluateCocycle C D e he n (Cohomology.Singular.Representatives.cochainBoundaryMap D n c) (Cohomology.Singular.ChainRepresentatives.chainClass C n z) = 0
  rw [evaluateCocycle_class]
  exact coboundary_cycle C D e he _ n c z

def homologyEvaluation (n : ℕ) : D.homology n →ₗ[F] (C.homology n →ₗ[R] F) :=
  ((Cohomology.Singular.Representatives.cochainBoundaries D n).liftQ (cocycleEvaluation C D e he n)
    (by
      rintro c ⟨w, rfl⟩
      exact cocycleEvaluation_boundary C D e he n w)).comp
    (Cohomology.Singular.Representatives.cohomologyQuotientIso D n).toLinearEquiv.toLinearMap

@[simp]
theorem homologyEvaluation_class_class (n : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles D n) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    homologyEvaluation C D e he n (Cohomology.Singular.Representatives.cochainClass D n c) (Cohomology.Singular.ChainRepresentatives.chainClass C n z) =
      e n c.val z.val := by
  dsimp only [homologyEvaluation, Cohomology.Singular.Representatives.cochainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact evaluateCocycle_class C D e he n c z

variable [Module.Injective R F]

theorem cochainClass_eq_zero (n : ℕ) (c : Cohomology.Singular.Representatives.cochainCocycles D n)
    (hc : ∀ z : Cohomology.Singular.ChainRepresentatives.chainCycles C n, e n c.val z.val = 0) :
    Cohomology.Singular.Representatives.cochainClass D n c = 0 := by
  obtain ⟨ψ, hψ⟩ := functional_factors (C.sc n).g.hom (e n c.val)
    (fun z hz => hc ⟨z, hz⟩)
  let p : (D.sc n).X₁ := (e ((ComplexShape.up ℕ).prev n)).symm ψ
  have hp : (D.sc n).f p = c.val := by
    apply (e n).injective
    change e n (D.d ((ComplexShape.up ℕ).prev n) n p) = e n c.val
    rw [he]
    have hep : e ((ComplexShape.up ℕ).prev n) p = ψ := (e _).apply_symm_apply ψ
    rw [hep]
    exact hψ
  exact (Cohomology.Singular.Representatives.cochainClass_eq_zero_iff D n c).mpr ⟨p, Subtype.ext hp⟩

theorem homologyEvaluation_injective (n : ℕ) :
    Function.Injective (homologyEvaluation C D e he n) := by
  intro a b hab
  have hz : homologyEvaluation C D e he n (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := Cohomology.Singular.Representatives.cochainClass_surjective D n (a - b)
  have hc0 : Cohomology.Singular.Representatives.cochainClass D n c = 0 := by
    apply cochainClass_eq_zero C D e he n c
    intro z
    have hv : homologyEvaluation C D e he n (Cohomology.Singular.Representatives.cochainClass D n c)
        (Cohomology.Singular.ChainRepresentatives.chainClass C n z) = 0 := by
      rw [hc, hz]
      rfl
    exact (homologyEvaluation_class_class C D e he n c z).symm.trans hv
  exact sub_eq_zero.mp (hc.symm.trans hc0)

theorem homologyEvaluation_surjective (n : ℕ) :
    Function.Surjective (homologyEvaluation C D e he n) := by
  intro L
  obtain ⟨φ, hφ⟩ := functional_extends (Cohomology.Singular.ChainRepresentatives.chainCycles C n).subtype Subtype.val_injective
    (L.comp (Cohomology.Singular.ChainRepresentatives.chainClass C n))
  let c : D.X n := (e n).symm φ
  have hbound : φ.comp (C.sc n).f.hom = 0 := by
    ext z
    have hz := LinearMap.congr_fun hφ (Cohomology.Singular.ChainRepresentatives.chainBoundaryMap C n z)
    change φ ((C.sc n).f z) = L (Cohomology.Singular.ChainRepresentatives.chainClass C n (Cohomology.Singular.ChainRepresentatives.chainBoundaryMap C n z)) at hz
    rw [Cohomology.Singular.ChainRepresentatives.chainClass_boundary, map_zero] at hz
    exact hz
  have hc : c ∈ Cohomology.Singular.Representatives.cochainCocycles D n := by
    change D.d n ((ComplexShape.up ℕ).next n) c = 0
    apply (e _).injective
    rw [he, map_zero]
    have hec : e n c = φ := (e n).apply_symm_apply φ
    rw [hec]
    exact hbound
  refine ⟨Cohomology.Singular.Representatives.cochainClass D n ⟨c, hc⟩, ?_⟩
  ext h
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n h
  rw [homologyEvaluation_class_class]
  have hz := LinearMap.congr_fun hφ z
  simpa only [c, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    Submodule.subtype_apply] using hz

def universalCoefficientEquiv (n : ℕ) : D.homology n ≃ₗ[F] (C.homology n →ₗ[R] F) :=
  LinearEquiv.ofBijective (homologyEvaluation C D e he n)
    ⟨homologyEvaluation_injective C D e he n, homologyEvaluation_surjective C D e he n⟩

end InjectiveDuality

open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem rationalModuleInjective : Module.Injective ℤ ℚ := by
  let : CategoryTheory.Injective (ModuleCat.of ℤ ℚ) := Cohomology.Singular.IntegralCoefficientInjective.injective_restrictScalars_rat
  exact Module.injective_module_of_injective_object ℤ ℚ

private theorem relativeDual_d (X : TopCat.{0}) (A : Set X) (i j : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X i) :
    RelativeCochainDual.relativeCochainIntegralDualEquiv X A j
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d i j c) =
      (RelativeCochainDual.relativeCochainIntegralDualEquiv X A i c).comp
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d j i).hom := by
  ext z
  exact RelativeCochainDual.relativeCochainIntegralDualEquiv_d X A i j c z

/-- Canonical evaluation of actual relative rational cohomology on actual
relative integral homology, obtained by descending cochain evaluation. -/
def relativeRationalHomologyEvaluation (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n →ₗ[ℚ]
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n →ₗ[ℤ] ℚ) :=
  InjectiveDuality.homologyEvaluation (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)
    (RelativeCochainDual.relativeCochainIntegralDualEquiv X A) (relativeDual_d X A) n

/-- On representatives the descended pairing is exactly evaluation of the
given relative cochain on the given relative chain. -/
@[simp]
theorem relativeRationalHomologyEvaluation_class_class (X : TopCat.{0}) (A : Set X)
    (n : ℕ) (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) n)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    relativeRationalHomologyEvaluation X A n
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) n c)
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z) =
      RelativeCochainDual.relativeCochainIntegralDualEquiv X A n c.val z.val :=
  InjectiveDuality.homologyEvaluation_class_class (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)
    (RelativeCochainDual.relativeCochainIntegralDualEquiv X A) (relativeDual_d X A) n c z

/-- The relative rational universal-coefficient isomorphism, whose forward
map is the actual evaluation pairing, in every nonnegative degree. -/
def relativeRationalUniversalCoefficientEquiv (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n ≃ₗ[ℚ]
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n →ₗ[ℤ] ℚ) := by
  let : Module.Injective ℤ ℚ := rationalModuleInjective
  exact InjectiveDuality.universalCoefficientEquiv (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)
    (RelativeCochainDual.relativeCochainIntegralDualEquiv X A) (relativeDual_d X A) n

@[simp]
theorem relativeRationalUniversalCoefficientEquiv_apply (X : TopCat.{0}) (A : Set X)
    (n : ℕ) (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    relativeRationalUniversalCoefficientEquiv X A n c =
      relativeRationalHomologyEvaluation X A n c := rfl

/-- Pullback of relative cohomology is adjoint to the actual map on relative
homology under the canonical evaluation pairing. -/
theorem relativeRationalHomologyEvaluation_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B n)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n) :
    relativeRationalHomologyEvaluation X A n
        (HomologicalComplex.homologyMap
          (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) n c) z =
      relativeRationalHomologyEvaluation Y B n c
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h) n z) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) n c
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z
  rw [Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    relativeRationalHomologyEvaluation_class_class,
    relativeRationalHomologyEvaluation_class_class]
  exact RelativeCochainDual.relativeCochainIntegralDualEquiv_naturality f h n c.val z.val

/-- Vanishing of the actual relative integral homology implies vanishing of
the actual relative rational cohomology in the same degree. -/
theorem relativeRationalCohomology_isZero_of_homology_isZero
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (h : IsZero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n)) :
    IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) := by
  let : Subsingleton (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n) :=
    ModuleCat.isZero_iff_subsingleton.mp h
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun a b => (relativeRationalUniversalCoefficientEquiv X A n).injective
    (Subsingleton.elim _ _)⟩

end

end OAI.AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient
