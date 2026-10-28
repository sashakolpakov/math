import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.LinearQuotientDual
import OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient

/-! # Relative Chain D -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Geometric.RelativeChainD

/-!
# Genuine relative cochains as functionals on relative chains

Relative cochains are the actual kernel of restriction to the subspace.
Relative scalar chains are the actual cokernel of the subspace inclusion.
The absolute evaluation equivalence identifies the former with functionals
vanishing on the kernel of the latter's quotient projection.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Cycles

variable {R : Type} [CommRing R]

/-- Absolute evaluation intertwines restriction of cochains and inclusion of chains. -/
theorem singularDegreewiseChainDualEquiv_restriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M (TopCat.of A) n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n c) =
      (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n c).comp
        ((RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n).hom :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.degreewiseChainDualEquiv_pullback M (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X A)) n c

/-- A relative cochain restricts to zero on the subspace in each degree. -/
theorem relativeCochainInclusion_restriction_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) = 0 :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction M X A) n) c

/-- The actual absolute-chain functional associated to a relative cochain. -/
def relativeCochainAbsoluteDual (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n →ₗ[R]
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n →ₗ[R] M) :=
  (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).toLinearMap.comp
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n).hom

@[simp]
theorem relativeCochainAbsoluteDual_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    relativeCochainAbsoluteDual M X A n c =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) :=
  rfl

/-- Relative evaluation vanishes on every chain coming from the subspace. -/
theorem relativeCochainAbsoluteDual_comp_subspace (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (relativeCochainAbsoluteDual M X A n c).comp
        ((RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n).hom = 0 := by
  have h := singularDegreewiseChainDualEquiv_restriction M X A n
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c)
  rw [relativeCochainInclusion_restriction_apply, map_zero] at h
  exact h.symm

/-- Relative evaluation annihilates the exact kernel of the relative chain projection. -/
theorem relativeCochainAbsoluteDual_ker (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    LinearMap.ker ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom ≤
      LinearMap.ker (relativeCochainAbsoluteDual M X A n c) := by
  rw [RelativeScalarChains.Cycles.relativeScalarChainProjection_ker]
  rintro z ⟨a, rfl⟩
  exact LinearMap.congr_fun (relativeCochainAbsoluteDual_comp_subspace M X A n c) a

/-- A relative cochain is determined by its values on absolute chains. -/
theorem relativeCochainAbsoluteDual_injective (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Function.Injective (relativeCochainAbsoluteDual M X A n) := by
  intro c d h
  apply (ModuleCat.mono_iff_injective ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n)).mp
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainSequence_degreewiseShortExact M X A n).mono_f
  exact (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).injective h

/-- Every absolute functional vanishing on the relative projection kernel is represented
by an actual relative cochain. -/
theorem exists_relativeCochain_of_vanishes (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (φ : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n →ₗ[R] M)
    (hφ : LinearMap.ker ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom ≤
      LinearMap.ker φ) :
    ∃ c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n,
      relativeCochainAbsoluteDual M X A n c = φ := by
  let a := (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).symm φ
  have ha : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n a = 0 := by
    apply (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M (TopCat.of A) n).injective
    rw [map_zero, singularDegreewiseChainDualEquiv_restriction]
    change ((AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n)
      ((AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).symm φ)).comp _ = 0
    rw [LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro z
    have hz : (RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n z ∈
        LinearMap.ker ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom := by
      rw [RelativeScalarChains.Cycles.relativeScalarChainProjection_ker]
      exact ⟨z, rfl⟩
    exact hφ hz
  have ha' : a ∈ LinearMap.range ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n).hom := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]
    exact ha
  obtain ⟨c, hc⟩ := ha'
  refine ⟨c, ?_⟩
  rw [relativeCochainAbsoluteDual_apply, hc]
  exact (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).apply_symm_apply φ

/-- The actual relative cochain kernel is the annihilator of the actual
relative chain projection kernel. -/
def relativeCochainAnnihilatorEquiv (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n ≃ₗ[R]
      LinearQuotientDual.Cycles.kernelAnnihilator ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom M :=
  LinearEquiv.ofBijective
    ((relativeCochainAbsoluteDual M X A n).codRestrict _
      (fun c => relativeCochainAbsoluteDual_ker M X A n c))
    ⟨by
      intro c d h
      apply relativeCochainAbsoluteDual_injective M X A n
      exact congrArg Subtype.val h,
      by
      intro φ
      obtain ⟨c, hc⟩ := exists_relativeCochain_of_vanishes M X A n φ.val φ.property
      exact ⟨c, Subtype.ext hc⟩⟩

@[simp]
theorem relativeCochainAnnihilatorEquiv_val (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (relativeCochainAnnihilatorEquiv M X A n c).val = relativeCochainAbsoluteDual M X A n c :=
  rfl

/-- Relative singular cochains are exactly coefficient-valued linear functionals
on the actual relative scalar chains. -/
def relativeDegreewiseChainDualEquiv (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n ≃ₗ[R]
      ((RelativeScalarChains.Cycles.relativeScalarChains R X A).X n →ₗ[R] M) :=
  (relativeCochainAnnihilatorEquiv M X A n).trans
    (LinearQuotientDual.Cycles.quotientDualEquiv (M := M) ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom
      (RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective R X A n)).symm

/-- Evaluation on a projected chain is the ordinary absolute evaluation. -/
@[simp]
theorem relativeDegreewiseChainDualEquiv_projection (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n) :
    relativeDegreewiseChainDualEquiv M X A n c
        ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) z := by
  change (LinearQuotientDual.Cycles.quotientDualEquiv (M := M) ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom
    (RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective R X A n)).symm
      (relativeCochainAnnihilatorEquiv M X A n c)
        (((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom z) = _
  rw [LinearQuotientDual.Cycles.quotientDualEquiv_symm_apply]
  rfl

/-- The inverse duality has the same explicit evaluation formula. -/
theorem relativeDegreewiseChainDualEquiv_symm_projection (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (φ : (RelativeScalarChains.Cycles.relativeScalarChains R X A).X n →ₗ[R] M)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n
          ((relativeDegreewiseChainDualEquiv M X A n).symm φ)) z =
      φ ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z) := by
  have h := relativeDegreewiseChainDualEquiv_projection M X A n
    ((relativeDegreewiseChainDualEquiv M X A n).symm φ) z
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- On a projected genuine singular simplex, the relative functional evaluates
the relative cochain's absolute image on that same simplex. -/
@[simp]
theorem relativeDegreewiseChainDualEquiv_simplex (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    relativeDegreewiseChainDualEquiv M X A n c
        ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (TopCat.toSSet.obj X) s)) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) := by
  rw [relativeDegreewiseChainDualEquiv_projection]
  exact AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex (TopCat.toSSet.obj X) M _ s

/-- The relative cochain differential is dual to the actual relative chain
differential, for all indices. -/
theorem relativeDegreewiseChainDualEquiv_d (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (i j : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X i) :
    relativeDegreewiseChainDualEquiv M X A j ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d i j c) =
      (relativeDegreewiseChainDualEquiv M X A i c).comp
        ((RelativeScalarChains.Cycles.relativeScalarChains R X A).d j i).hom := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective R X A j z
  simp only [LinearMap.comp_apply]
  rw [relativeDegreewiseChainDualEquiv_projection]
  have hp := ConcreteCategory.congr_hom ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).comm j i) z
  change (RelativeScalarChains.Cycles.relativeScalarChains R X A).d j i ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f j z) =
    (RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f i ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d j i z) at hp
  rw [hp, relativeDegreewiseChainDualEquiv_projection]
  have hi := ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).comm i j) c
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d i j ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f i c) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f j ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d i j c) at hi
  rw [← hi]
  exact LinearMap.congr_fun (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_d (TopCat.toSSet.obj X) M i j
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f i c)) z

/-- The actual relative cochain complex is the actual linear Hom complex of
the relative scalar chains. -/
def relativeCochainDualIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A ≅ DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex (RelativeScalarChains.Cycles.relativeScalarChains R X A) M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (relativeDegreewiseChainDualEquiv M X A n).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change (relativeDegreewiseChainDualEquiv M X A i c).comp
        ((RelativeScalarChains.Cycles.relativeScalarChains R X A).d j i).hom =
          relativeDegreewiseChainDualEquiv M X A j ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d i j c)
      exact (relativeDegreewiseChainDualEquiv_d M X A i j c).symm)

@[simp]
theorem relativeCochainDualIso_hom_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (relativeCochainDualIso M X A).hom.f n c = relativeDegreewiseChainDualEquiv M X A n c :=
  rfl

@[simp]
theorem relativeCochainDualIso_inv_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (φ : (RelativeScalarChains.Cycles.relativeScalarChains R X A).X n →ₗ[R] M) :
    (relativeCochainDualIso M X A).inv.f n φ = (relativeDegreewiseChainDualEquiv M X A n).symm φ :=
  rfl

/-- Scalar-valued relative cochains are the genuine linear dual cochain complex. -/
abbrev relativeScalarCochainDualIso (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A ≅
      DualComplexUniversalCoefficient.Cycles.dualCochainComplex (RelativeScalarChains.Cycles.relativeScalarChains R X A) :=
  relativeCochainDualIso (ModuleCat.of R R) X A

end Cycles

end AlgebraicGeometry.CycleClass.Geometric.RelativeChainD

namespace AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles
open _root_.CategoryTheory
section

/-!
# Canonical universal-coefficient duality for relative singular cohomology

The cohomology of the actual relative cochain kernel is identified with the
dual of the homology of the actual relative scalar-chain cokernel. The map is
ordinary evaluation on representatives, descended through both boundaries.
-/

section Evaluation

variable {R : Type} [CommRing R]

/-- Canonical evaluation of actual relative cohomology on actual relative homology. -/
def relativeHomologyEvaluation (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n →ₗ[R]
      (RelativeScalarChains.Cycles.relativeScalarHomology R X A n →ₗ[R] M) :=
  (DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation (RelativeScalarChains.Cycles.relativeScalarChains R X A) M n).comp
    (HomologicalComplex.homologyMap (relativeCochainDualIso M X A).hom n).hom

/-- On genuine cocycle and cycle representatives the descended evaluation is
the actual relative-chain functional. -/
@[simp]
theorem relativeHomologyEvaluation_class_class (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains R X A) n) :
    relativeHomologyEvaluation M X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n c)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains R X A) n z) =
        relativeDegreewiseChainDualEquiv M X A n c.val z.val := by
  change DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation (RelativeScalarChains.Cycles.relativeScalarChains R X A) M n
    ((HomologicalComplex.homologyMap (relativeCochainDualIso M X A).hom n)
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n c))
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains R X A) n z) = _
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation_class_class]
  rfl

/-- A projected relative cycle evaluates by the original absolute singular-chain
functional, even when its absolute representative is not an absolute cycle. -/
theorem relativeHomologyEvaluation_class_projection (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n)
    (hz : (RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains R X A) n) :
    relativeHomologyEvaluation M X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n c)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains R X A) n
        ⟨(RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z, hz⟩) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c.val) z := by
  rw [relativeHomologyEvaluation_class_class]
  exact relativeDegreewiseChainDualEquiv_projection M X A n c.val z

end Evaluation

variable (F : Type) [Field F]

/-- The universal-coefficient isomorphism for the genuine singular cohomology
and homology of any topological pair over a field, including degree zero. -/
def relativeUniversalCoefficientEquiv (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n ≃ₗ[F]
      Module.Dual F (RelativeScalarChains.Cycles.relativeScalarHomology F X A n) :=
  (((HomologicalComplex.homologyFunctor (ModuleCat.{0} F) (ComplexShape.up ℕ) n).mapIso
    (relativeScalarCochainDualIso F X A)).toLinearEquiv).trans
      (DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv (RelativeScalarChains.Cycles.relativeScalarChains F X A) n)

/-- The equivalence's forward map is precisely the canonical relative evaluation. -/
@[simp]
theorem relativeUniversalCoefficientEquiv_apply (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n) :
    relativeUniversalCoefficientEquiv F X A n c =
      relativeHomologyEvaluation (ModuleCat.of F F) X A n c := rfl

/-- Universal-coefficient duality sends relative cocycle classes to their actual
evaluation on relative cycle classes. -/
@[simp]
theorem relativeUniversalCoefficientEquiv_class_class
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of F F) X A) n)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains F X A) n) :
    relativeUniversalCoefficientEquiv F X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of F F) X A) n c)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains F X A) n z) =
        relativeDegreewiseChainDualEquiv (ModuleCat.of F F) X A n c.val z.val :=
  relativeHomologyEvaluation_class_class (ModuleCat.of F F) X A n c z

/-- On a projected relative cycle the universal-coefficient equivalence computes
the same ordinary singular-chain evaluation as the cochain's absolute image. -/
theorem relativeUniversalCoefficientEquiv_class_projection
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of F F) X A) n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).X n)
    (hz : (RelativeScalarChains.Cycles.relativeScalarChainProjection F X A).f n z ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains F X A) n) :
    relativeUniversalCoefficientEquiv F X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of F F) X A) n c)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains F X A) n
        ⟨(RelativeScalarChains.Cycles.relativeScalarChainProjection F X A).f n z, hz⟩) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of F F) X n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of F F) X A).f n c.val) z :=
  relativeHomologyEvaluation_class_projection (ModuleCat.of F F) X A n c z hz

end

/-!
# Relative cohomology detects actual relative homology

The genuine field universal-coefficient equivalence identifies every linear
functional on relative scalar homology with an actual relative cohomology
class. Algebraic dual separation therefore detects classes in the original
relative homology group, without a finite-dimensionality or duality premise.
-/

variable (F : Type) [Field F] (X : TopCat.{0}) (A : Set X) (n : ℕ)

/-- Every nonzero actual relative homology class has a relative cohomology
test whose genuine evaluation on it is one. -/
theorem exists_relativeCohomology_evaluation_eq_one
    {z : RelativeScalarChains.Cycles.relativeScalarHomology F X A n} (hz : z ≠ 0) :
    ∃ c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n,
      relativeUniversalCoefficientEquiv F X A n c z = 1 := by
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one F hz
  refine ⟨(relativeUniversalCoefficientEquiv F X A n).symm L, ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact hL

/-- Vanishing of all actual relative cohomology evaluations is equivalent
to vanishing of the original relative homology class. -/
theorem relativeScalarHomology_eq_zero_iff_evaluation
    (z : RelativeScalarChains.Cycles.relativeScalarHomology F X A n) :
    z = 0 ↔ ∀ c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n,
      relativeUniversalCoefficientEquiv F X A n c z = 0 := by
  constructor
  · rintro rfl c
    exact map_zero (relativeUniversalCoefficientEquiv F X A n c)
  · intro h
    by_contra hz
    obtain ⟨c, hc⟩ := exists_relativeCohomology_evaluation_eq_one F X A n hz
    exact one_ne_zero (hc.symm.trans (h c))

/-- The full family of genuine relative cohomology evaluations separates
relative homology classes, in every degree and over every field. -/
theorem relativeScalarHomology_eq_iff_evaluation
    (z w : RelativeScalarChains.Cycles.relativeScalarHomology F X A n) :
    z = w ↔ ∀ c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n,
      relativeUniversalCoefficientEquiv F X A n c z =
        relativeUniversalCoefficientEquiv F X A n c w := by
  constructor
  · rintro rfl c
    rfl
  · intro h
    apply sub_eq_zero.mp
    apply (relativeScalarHomology_eq_zero_iff_evaluation F X A n (z - w)).mpr
    intro c
    rw [map_sub, h c, sub_self]

end AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles

end

end OAI
