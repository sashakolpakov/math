import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeSingularCochainBridge
import OAI.AlgebraicTopology.Singular.RelativeCochainIntMap
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Relative Dual Absolute Extension -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.RelativeDualAbsoluteExtension

noncomputable section

section

/-! # Actual relative comparisons retain pullback and forgetting the support -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicTopology.Singular

variable (R : Type) [CommRing R]

/-- The canonical map of the literal subset pairs. -/
def originalSubsetPairMap {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) : TopPair.ofSubset A ⟶ TopPair.ofSubset B :=
  TopPair.ofHom f (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The relative comparison intertwines actual continuous maps of pairs. -/
theorem relativeSingularCochainBridgeIso_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of R R) f h ≫
        (RelativeSingularCochainBridge.relativeSingularCochainBridgeIso R X A).hom =
      (RelativeSingularCochainBridge.relativeSingularCochainBridgeIso R Y B).hom ≫
        AlgebraicTopology.Singular.Cohomology.relativeCochainComplexMap R (originalSubsetPairMap f h) := by
  let s := AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexNat R (TopPair.ofSubset A)
  let : Mono s.f := (RelativeSingularCochainBridge.originalRelativeCochainSequence_shortExact R X A).mono_f
  apply (cancel_mono s.f).mp
  rw [Category.assoc, RelativeSingularCochainBridge.relativeSingularCochainBridgeIso_inclusion,
    ← Category.assoc, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality, Category.assoc,
    SingularCochainBridge.singularCochainBridgeIso_naturality]
  have hc := (AlgebraicTopology.Singular.RelativeCochainIntMap.relativeDualCochainShortComplexNatMap R (originalSubsetPairMap f h)).comm₁₂
  change AlgebraicTopology.Singular.Cohomology.relativeCochainComplexMap R (originalSubsetPairMap f h) ≫ s.f =
    (AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexNat R (TopPair.ofSubset B)).f ≫
      AlgebraicTopology.Singular.CohomologyTo.singularCochainComplexMap R f at hc
  rw [Category.assoc, hc]
  simpa only [← Category.assoc] using
    congrArg (fun g => g ≫ AlgebraicTopology.Singular.CohomologyTo.singularCochainComplexMap R f)
      (RelativeSingularCochainBridge.relativeSingularCochainBridgeIso_inclusion R Y B).symm

set_option backward.isDefEq.respectTransparency false in
/-- The induced equivalence retains the actual relative-to-absolute cohomology map. -/
theorem relativeSingularCohomologyBridgeEquiv_toAbsolute (X : TopCat.{0}) (A : Set X)
    (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) X A n) :
    AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute R (TopPair.ofSubset A) n
        (RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv R X A n c) =
      SingularCochainBridge.singularCohomologyBridgeEquiv R X n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of R R) X A n c) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (RelativeSingularCochainBridge.relativeSingularCochainBridgeIso_inclusion R X A)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

set_option backward.isDefEq.respectTransparency false in
/-- The induced equivalence retains every actual relative cohomology pullback. -/
theorem relativeSingularCohomologyBridgeEquiv_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) Y B n) :
    RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv R X A n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) f h n c) =
      AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap R n (originalSubsetPairMap f h)
        (RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv R Y B n c) := by
  have he := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (relativeSingularCochainBridgeIso_naturality R f h)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact ConcreteCategory.congr_hom he c

end

/-! # The original integer-degree relative inclusion forgets to the actual absolute class -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.HomologicalComplex OAI.AlgebraicTopology.Singular

variable (R : Type) [CommRing R]

theorem relativeDualAbsoluteExtension (P : TopPair.{0}) (n : ℕ)
    (a : (AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt R P).X₁.homology (n : ℤ)) :
    AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute R P n (AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv R P n a) =
      ((AlgebraicTopology.Singular.CohomologyTo.SingularCochainComplex R P.fst).extendHomologyIso
        ComplexShape.embeddingUpNat rfl).hom
        (homologyMap (AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt R P).f (n : ℤ) a) := by
  simpa only [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply] using!
    ConcreteCategory.congr_hom
      (HomologicalComplex.extendHomologyIso_hom_naturality
        (AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexNat R P).f ComplexShape.embeddingUpNat
        (j := n) (j' := (n : ℤ)) rfl).symm a

theorem relativeToAbsolute_naturality {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology R Q n) :
    AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute R P n (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap R n f a) =
      AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n f.right (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute R Q n a) := by
  have h := (AlgebraicTopology.Singular.RelativeCochainIntMap.relativeDualCochainShortComplexNatMap R f).comm₁₂
  simpa only [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply] using!
    ConcreteCategory.congr_hom (congrArg (fun g => homologyMap g n) h) a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.RelativeDualAbsoluteExtension
