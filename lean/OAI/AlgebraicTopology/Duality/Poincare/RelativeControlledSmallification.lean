import OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap
import OAI.AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Relative Controlled Smallification -/

namespace OAI.AlgebraicTopology.Duality.Poincare.RelativeControlledSmallification

noncomputable section

/-!
# Support-controlled smallification on actual relative chains

The genuine smallification operator and its genuine homotopy preserve chains
on every subspace. They therefore descend through the actual relative-chain
cokernel for any subset. The descended operator is homotopic to the identity,
and every relative cycle has a representative obtained by projecting the
smallification of an ordinary chain lift.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)
variable (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

/-- Smallification preserves the kernel of the actual relative-chain projection. -/
theorem smallificationEndomorphism_relativeKernel (A : Set X) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c = 0) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
      ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c) = 0 := by
  have hmem : c ∈ AlgebraicGeometry.CycleClass.Geometric.ControlledChainSupport.Cycles.singularSubspaceImage X A n := by
    change c ∈ LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom
    rw [← AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport.Cycles.relativeChainProjection_ker X A n]
    exact hc
  change (AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c ∈
    LinearMap.ker ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n).hom
  rw [AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport.Cycles.relativeChainProjection_ker]
  exact AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism_subspace X U hopen hcover n A c hmem

/-- The ambient operator kills subspace chains after projection to relative chains. -/
theorem smallificationEndomorphism_subspace_projection_zero (A : Set X) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A ≫
      (AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
    ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f n c)) = 0
  apply smallificationEndomorphism_relativeKernel X U hopen hcover A n
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion_projection X A) n) c

/-- The unique actual relative-chain operator induced by ambient smallification. -/
def relativeSmallificationEndomorphism (A : Set X) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A :=
  cokernel.desc (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A)
    (AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A)
    (smallificationEndomorphism_subspace_projection_zero X U hopen hcover A)

/-- Projection commutes with the descended smallification as an equality of chain maps. -/
@[reassoc]
theorem relativeSmallificationEndomorphism_projection (A : Set X) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A ≫ relativeSmallificationEndomorphism X U hopen hcover A =
      AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A :=
  cokernel.π_desc _ _ _

/-- The descended operator is computed on any ordinary chain representative. -/
@[simp]
theorem relativeSmallificationEndomorphism_projection_apply (A : Set X) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (relativeSmallificationEndomorphism X U hopen hcover A).f n
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
        ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom
      (relativeSmallificationEndomorphism_projection X U hopen hcover A) n) c

/-- Every actual ambient homotopy component also kills subspace chains after projection. -/
theorem smallificationHomotopy_subspace_projection_zero (A : Set X) (a b : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f a ≫
      AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationHomotopyComponent X U hopen hcover a b ≫
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f b = 0 := by
  by_cases hab : a + 1 = b
  · subst b
    rw [AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationHomotopyComponent_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change AlgebraicGeometry.CycleClass.Geometric.ControlledSmallification.Cycles.smallificationHomotopyDegree X U hopen hcover a
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f a c) ∈
        LinearMap.ker ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (a + 1)).hom
    rw [AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport.Cycles.relativeChainProjection_ker]
    exact AlgebraicGeometry.CycleClass.Geometric.ControlledSmallification.Cycles.smallificationHomotopyDegree_subspace X U hopen hcover a A _ ⟨c, rfl⟩
  · rw [AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationHomotopyComponent_zero X U hopen hcover a b hab,
      zero_comp, comp_zero]

/-- The ambient support-controlled homotopy descends to a genuine homotopy
from the identity to the actual relative smallification operator. -/
def relativeSmallificationHomotopy (A : Set X) :
    Homotopy (𝟙 (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A))
      (relativeSmallificationEndomorphism X U hopen hcover A) :=
  AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent.Cycles.descendHomotopy (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence X A) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence X A)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_shortExact X A)
    (by
      change AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A ≫ 𝟙 _ = 𝟙 _ ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A
      simp only [Category.comp_id, Category.id_comp])
    (by
      rw [AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationChainMap_inclusion]
      exact relativeSmallificationEndomorphism_projection X U hopen hcover A)
    (AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationAmbientHomotopy X U hopen hcover)
    (smallificationHomotopy_subspace_projection_zero X U hopen hcover A)

/-- Projection of each descended homotopy component is the original support-controlled component. -/
@[reassoc]
theorem relativeSmallificationHomotopy_projection (A : Set X) (a b : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f a ≫
      (relativeSmallificationHomotopy X U hopen hcover A).hom a b =
        AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationHomotopyComponent X U hopen hcover a b ≫
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f b :=
  AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent.Cycles.quotientHomotopyComponent_projection
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence X A) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence X A)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_shortExact X A)
    (AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationAmbientHomotopy X U hopen hcover)
    (smallificationHomotopy_subspace_projection_zero X U hopen hcover A) a b

/-- The descended homotopy has the same concrete formula on any ordinary representative. -/
@[simp]
theorem relativeSmallificationHomotopy_projection_apply (A : Set X) (a b : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X a) :
    (relativeSmallificationHomotopy X U hopen hcover A).hom a b
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f a c) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f b
        (AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationHomotopyComponent X U hopen hcover a b c) :=
  ConcreteCategory.congr_hom
    (relativeSmallificationHomotopy_projection X U hopen hcover A a b) c

/-- Relative smallification induces exactly the identity on actual homology. -/
@[simp]
theorem relativeSmallificationEndomorphism_homologyMap (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap
      (relativeSmallificationEndomorphism X U hopen hcover A) n =
        𝟙 ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).homology n) := by
  have h := (relativeSmallificationHomotopy X U hopen hcover A).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_id] at h
  exact h.symm

/-- The concrete image of any actual relative cycle represents the same homology class. -/
@[simp]
theorem relativeSmallificationEndomorphism_chainClass (A : Set X) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (relativeSmallificationEndomorphism X U hopen hcover A) n z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z := by
  rw [← Cohomology.Singular.EvaluationNaturality.chainClass_naturality, relativeSmallificationEndomorphism_homologyMap]
  rfl

/-- Smallifying an ordinary lift of a relative cycle still gives a relative cycle;
the lift is not required to be an absolute cycle. -/
theorem projectedSmallification_mem_cycles (A : Set X) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
      ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n := by
  rw [← relativeSmallificationEndomorphism_projection_apply]
  exact (Cohomology.Singular.EvaluationNaturality.chainCycleMap (relativeSmallificationEndomorphism X U hopen hcover A) n
    ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c, hc⟩).property

/-- Every ordinary lift of a relative cycle gives an explicit smallified
representative of the same relative homology class. -/
theorem projectedSmallification_chainClass (A : Set X) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n
        ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
          ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c),
          projectedSmallification_mem_cycles X U hopen hcover A n c hc⟩ =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n
        ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c, hc⟩ := by
  have h := relativeSmallificationEndomorphism_chainClass X U hopen hcover A n
    ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c, hc⟩
  convert h using 1
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n)
  apply Subtype.ext
  exact (relativeSmallificationEndomorphism_projection_apply X U hopen hcover A n c).symm

/-- The ordinary boundary of a smallified relative-cycle lift projects to zero,
even though the lift need not have zero ordinary boundary. -/
theorem projectedSmallification_boundary_zero (A : Set X) (n i : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f i
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d n i
        ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c)) = 0 := by
  have hz := Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n i
    ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
      ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c),
      projectedSmallification_mem_cycles X U hopen hcover A n c hc⟩
  have hd := ConcreteCategory.congr_hom ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).comm n i)
    ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c)
  exact hd.symm.trans hz

/-- An actual relative cycle admits an ordinary lift whose actual smallification
is cover-small and represents the same relative homology class after projection. -/
theorem exists_smallified_relativeCycle_representative (A : Set X) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    ∃ c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n,
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c = z.val ∧
      (AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c ∈
        LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom ∧
      ∃ hc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
          ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c) ∈
            Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n,
        Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n
          ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
            ((AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X U hopen hcover).f n c), hc⟩ =
          Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z := by
  have hsurj : Function.Surjective ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n) :=
    (ModuleCat.epi_iff_surjective _).mp
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_degreewiseShortExact X A n).epi_g
  obtain ⟨c, hc⟩ := hsurj z.val
  have hcycle : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n := by
    rw [hc]
    exact z.property
  refine ⟨c, hc, AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism_small X U hopen hcover n c,
    projectedSmallification_mem_cycles X U hopen hcover A n c hcycle, ?_⟩
  have h := projectedSmallification_chainClass X U hopen hcover A n c hcycle
  have heq : (⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c, hcycle⟩ :
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) = z := Subtype.ext hc
  rwa [heq] at h

end

end OAI.AlgebraicTopology.Duality.Poincare.RelativeControlledSmallification
