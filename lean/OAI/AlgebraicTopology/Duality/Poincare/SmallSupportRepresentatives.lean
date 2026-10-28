import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportCover
import OAI.AlgebraicTopology.Duality.Poincare.RelativeControlledSmallification
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf

/-! # Small Support Representatives -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SmallSupportRepresentatives

noncomputable section

/-!
# One genuine small-chain representative for two supports

The four-open support cover supplies a single actual smallification. Every
class supported on the union has a representative in that small-chain complex.
The same ordinary chain represents the restricted classes at every smaller
support, and its boundary vanishes after each of those relative projections.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles

variable (X : TopCat.{0}) (U V K L : Set X)

/-- Inclusion of the actual simultaneous small chains followed by a genuine relative quotient. -/
abbrev smallSupportRelativeProjection (A : Set X) :
    SmallSupportCover.smallSupportScalarChains ℤ X U V K L ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A :=
  SmallSupportCover.smallSupportChainInclusion ℤ X U V K L ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A

@[simp]
theorem smallSupportRelativeProjection_apply (A : Set X) (n : ℕ)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n) :
    (smallSupportRelativeProjection X U V K L A).f n s =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
        ((SmallSupportCover.smallSupportChainInclusion ℤ X U V K L).f n s) := rfl

/-- Restricting the support retains exactly the same ambient small chain. -/
@[reassoc]
theorem smallSupportRelativeProjection_restriction {S T : Set X} (hST : S ⊆ T) :
    smallSupportRelativeProjection X U V K L Tᶜ ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hST =
      smallSupportRelativeProjection X U V K L Sᶜ := by
  exact (Category.assoc (SmallSupportCover.smallSupportChainInclusion ℤ X U V K L)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Tᶜ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hST)).trans
      (congrArg (fun f => SmallSupportCover.smallSupportChainInclusion ℤ X U V K L ≫ f)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_projection X hST))

/-- A relative cycle at a support remains a relative cycle at every smaller support. -/
theorem smallSupportRelativeCycle_restrict {S T : Set X} (hST : S ⊆ T)
    (n : ℕ) (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (smallSupportRelativeProjection X U V K L Tᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Tᶜ) n) :
    (smallSupportRelativeProjection X U V K L Sᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Sᶜ) n := by
  have hz := (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hST) n
    ⟨(smallSupportRelativeProjection X U V K L Tᶜ).f n s, hs⟩).property
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom
      (smallSupportRelativeProjection_restriction X U V K L hST) n) s
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hST).f n
    ((smallSupportRelativeProjection X U V K L Tᶜ).f n s) =
      (smallSupportRelativeProjection X U V K L Sᶜ).f n s at hp
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hST).f n
    ((smallSupportRelativeProjection X U V K L Tᶜ).f n s) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Sᶜ) n at hz
  rwa [hp] at hz

/-- The all-index boundary of a small relative cycle projects to zero. -/
theorem smallSupportRelativeCycle_boundary_zero (A : Set X) (n i : ℕ)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (smallSupportRelativeProjection X U V K L A).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    (smallSupportRelativeProjection X U V K L A).f i
      ((SmallSupportCover.smallSupportScalarChains ℤ X U V K L).d n i s) = 0 := by
  have hz := Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n i
    ⟨(smallSupportRelativeProjection X U V K L A).f n s, hs⟩
  have hd := ConcreteCategory.congr_hom
    ((smallSupportRelativeProjection X U V K L A).comm n i) s
  exact hd.symm.trans hz

/-- The same boundary statement in the ordinary ambient singular-chain complex. -/
theorem smallSupportRelativeCycle_ambient_boundary_zero (A : Set X) (n i : ℕ)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (smallSupportRelativeProjection X U V K L A).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f i
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d n i
        ((SmallSupportCover.smallSupportChainInclusion ℤ X U V K L).f n s)) = 0 := by
  have hz := Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n i
    ⟨(smallSupportRelativeProjection X U V K L A).f n s, hs⟩
  have hd := ConcreteCategory.congr_hom ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).comm n i)
    ((SmallSupportCover.smallSupportChainInclusion ℤ X U V K L).f n s)
  exact hd.symm.trans hz

/-- A single union-relative cycle has zero projected boundary at every smaller support. -/
theorem smallSupportUnionCycle_boundary_zero (S : Set X) (hS : S ⊆ K ∪ L)
    (n i : ℕ) (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Sᶜ).f i
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d n i
        ((SmallSupportCover.smallSupportChainInclusion ℤ X U V K L).f n s)) = 0 :=
  smallSupportRelativeCycle_ambient_boundary_zero X U V K L Sᶜ n i s
    (smallSupportRelativeCycle_restrict X U V K L hS n s hs)

theorem smallSupportUnionCycle_boundary_left (n i : ℕ)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f i
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d n i
        ((SmallSupportCover.smallSupportChainInclusion ℤ X U V K L).f n s)) = 0 :=
  smallSupportUnionCycle_boundary_zero X U V K L K Set.subset_union_left n i s hs

theorem smallSupportUnionCycle_boundary_right (n i : ℕ)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Lᶜ).f i
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d n i
        ((SmallSupportCover.smallSupportChainInclusion ℤ X U V K L).f n s)) = 0 :=
  smallSupportUnionCycle_boundary_zero X U V K L L Set.subset_union_right n i s hs

theorem smallSupportUnionCycle_boundary_intersection (n i : ℕ)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (K ∩ L)ᶜ).f i
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d n i
        ((SmallSupportCover.smallSupportChainInclusion ℤ X U V K L).f n s)) = 0 :=
  smallSupportUnionCycle_boundary_zero X U V K L (K ∩ L)
    (fun _ hx => Or.inl hx.1) n i s hs

/-- Restriction on native homology is represented by the same literal small chain. -/
theorem smallSupportRelativeClass_restriction {S T : Set X} (hST : S ⊆ T)
    (n : ℕ) (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hT : (smallSupportRelativeProjection X U V K L Tᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Tᶜ) n)
    (hS : (smallSupportRelativeProjection X U V K L Sᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Sᶜ) n) :
    HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hST) n
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Tᶜ) n
          ⟨(smallSupportRelativeProjection X U V K L Tᶜ).f n s, hT⟩) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Sᶜ) n
        ⟨(smallSupportRelativeProjection X U V K L Sᶜ).f n s, hS⟩ := by
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Sᶜ) n)
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom
      (smallSupportRelativeProjection_restriction X U V K L hST) n) s

variable (hU : IsOpen U) (hV : IsOpen V) (hK : IsClosed K) (hL : IsClosed L)
variable (hKU : K ⊆ U) (hLV : L ⊆ V)

include hU hV hK hL hKU hLV

/-- Every actual class supported on the union has an actual simultaneous
small-chain representative. No absolute-cycle lift is assumed. -/
theorem exists_smallSupportRepresentative (n : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (K ∪ L)ᶜ n) :
    ∃ (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
      (hs : (smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n),
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n
        ⟨(smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s, hs⟩ = z := by
  obtain ⟨cycle, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n z
  obtain ⟨c, _hc, _hsmall, hcycle, hclass⟩ :=
    RelativeControlledSmallification.exists_smallified_relativeCycle_representative X (SmallSupportCover.smallSupportCover X U V K L)
      (SmallSupportCover.smallSupportCover_isOpen X U V K L hU hV hK hL)
      (SmallSupportCover.smallSupportCover_covers X U V K L hKU hLV) (K ∪ L)ᶜ n cycle
  let s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n :=
    (SmallSupportCover.smallSupportSmallification X U V K L hU hV hK hL hKU hLV).f n c
  have heq : (SmallSupportCover.smallSupportChainInclusion ℤ X U V K L).f n s =
      (AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X (SmallSupportCover.smallSupportCover X U V K L)
        (SmallSupportCover.smallSupportCover_isOpen X U V K L hU hV hK hL)
        (SmallSupportCover.smallSupportCover_covers X U V K L hKU hLV)).f n c :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom
        (SmallSupportCover.smallSupportSmallification_inclusion X U V K L hU hV hK hL hKU hLV) n) c
  have hs : (smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n := by
    rw [smallSupportRelativeProjection_apply, heq]
    exact hcycle
  refine ⟨s, hs, ?_⟩
  convert hclass using 1
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n)
  apply Subtype.ext
  exact congrArg ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (K ∪ L)ᶜ).f n) heq

/-- One small chain simultaneously represents the union class and all its
actual support restrictions, in particular at K, L, and their intersection. -/
theorem exists_commonSmallSupportRepresentative (n : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (K ∪ L)ᶜ n) :
    ∃ (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
      (hs : (smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n),
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n
        ⟨(smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s, hs⟩ = z ∧
      ∀ (S : Set X) (hS : S ⊆ K ∪ L),
        ∃ hcycle : (smallSupportRelativeProjection X U V K L Sᶜ).f n s ∈
            Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Sᶜ) n,
          Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Sᶜ) n
              ⟨(smallSupportRelativeProjection X U V K L Sᶜ).f n s, hcycle⟩ =
            HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hS) n z := by
  obtain ⟨s, hs, hclass⟩ :=
    exists_smallSupportRepresentative X U V K L hU hV hK hL hKU hLV n z
  refine ⟨s, hs, hclass, ?_⟩
  intro S hS
  let hcycle := smallSupportRelativeCycle_restrict X U V K L hS n s hs
  refine ⟨hcycle, ?_⟩
  have h := smallSupportRelativeClass_restriction X U V K L hS n s hs hcycle
  rw [hclass] at h
  exact h.symm

end

end OAI.AlgebraicTopology.Duality.Poincare.SmallSupportRepresentatives
