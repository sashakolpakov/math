import OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion
import OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallEquivalence
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Small Support Cover -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SmallSupportCover

noncomputable section

section

/-!
# A simultaneous small-chain cover for two closed supports

The four intersections of the covers `{U, Kᶜ}` and `{V, Lᶜ}` form an actual
open cover when the closed supports lie in their respective opens. Its small
singular subcomplex maps canonically to both binary small subcomplexes and to
the binary subcomplex for `{U ∩ V, (K ∩ L)ᶜ}`. All maps retain the original
ambient singular simplex, and therefore commute with the actual ambient
chain inclusions.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

section Cover

variable (X : TopCat.{0}) (U V K L : Set X)

/-- The four actual subsets used for simultaneous smallness at two supports. -/
def smallSupportCover (b : Bool × Bool) : Set X :=
  (if b.1 then Kᶜ else U) ∩ (if b.2 then Lᶜ else V)

@[simp]
theorem smallSupportCover_false_false :
    smallSupportCover X U V K L (false, false) = U ∩ V := rfl

@[simp]
theorem smallSupportCover_false_true :
    smallSupportCover X U V K L (false, true) = U ∩ Lᶜ := rfl

@[simp]
theorem smallSupportCover_true_false :
    smallSupportCover X U V K L (true, false) = Kᶜ ∩ V := rfl

@[simp]
theorem smallSupportCover_true_true :
    smallSupportCover X U V K L (true, true) = Kᶜ ∩ Lᶜ := rfl

/-- Closed supports and open ambient neighborhoods make all four members open. -/
theorem smallSupportCover_isOpen (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsClosed K) (hL : IsClosed L) (b : Bool × Bool) :
    IsOpen (smallSupportCover X U V K L b) := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c
  · exact hU.inter hV
  · exact hU.inter hL.isOpen_compl
  · exact hK.isOpen_compl.inter hV
  · exact hK.isOpen_compl.inter hL.isOpen_compl

/-- Every point belongs to one of the four subsets if each support lies in its open. -/
theorem smallSupportCover_covers (hKU : K ⊆ U) (hLV : L ⊆ V) (x : X) :
    ∃ b, x ∈ smallSupportCover X U V K L b := by
  classical
  by_cases hxK : x ∈ K
  · by_cases hxL : x ∈ L
    · exact ⟨(false, false), hKU hxK, hLV hxL⟩
    · exact ⟨(false, true), hKU hxK, hxL⟩
  · by_cases hxL : x ∈ L
    · exact ⟨(true, false), hxK, hLV hxL⟩
    · exact ⟨(true, true), hxK, hxL⟩

/-- The first projection of indices refines the cover at `K`. -/
theorem smallSupportCover_subset_left (b : Bool × Bool) :
    smallSupportCover X U V K L b ⊆ if b.1 then Kᶜ else U :=
  Set.inter_subset_left

/-- The second projection of indices refines the cover at `L`. -/
theorem smallSupportCover_subset_right (b : Bool × Bool) :
    smallSupportCover X U V K L b ⊆ if b.2 then Lᶜ else V :=
  Set.inter_subset_right

/-- Boolean disjunction of the indices refines the intersection-support cover. -/
theorem smallSupportCover_subset_intersection (b : Bool × Bool) :
    smallSupportCover X U V K L b ⊆ if b.1 || b.2 then (K ∩ L)ᶜ else U ∩ V := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c
  · exact Set.Subset.rfl
  · intro x hx hKL
    exact hx.2 hKL.2
  · intro x hx hKL
    exact hx.1 hKL.1
  · intro x hx hKL
    exact hx.1 hKL.1

/-- The genuine small singular simplicial subcomplex for the four-cover. -/
abbrev smallSupportSubcomplex : (TopCat.toSSet.obj X).Subcomplex :=
  DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X (smallSupportCover X U V K L)

theorem smallSupportSubcomplex_le_left :
    smallSupportSubcomplex X U V K L ≤ AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X U Kᶜ := by
  rw [AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex_eq]
  exact DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex_le_of_refinement X (smallSupportCover X U V K L)
    (fun b : Bool => if b then Kᶜ else U)
    (fun b => ⟨b.1, smallSupportCover_subset_left X U V K L b⟩)

theorem smallSupportSubcomplex_le_right :
    smallSupportSubcomplex X U V K L ≤ AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X V Lᶜ := by
  rw [AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex_eq]
  exact DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex_le_of_refinement X (smallSupportCover X U V K L)
    (fun b : Bool => if b then Lᶜ else V)
    (fun b => ⟨b.2, smallSupportCover_subset_right X U V K L b⟩)

theorem smallSupportSubcomplex_le_intersection :
    smallSupportSubcomplex X U V K L ≤
      AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∩ V) (K ∩ L)ᶜ := by
  rw [AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex_eq]
  exact DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex_le_of_refinement X (smallSupportCover X U V K L)
    (fun b : Bool => if b then (K ∩ L)ᶜ else U ∩ V)
    (fun b => ⟨b.1 || b.2, smallSupportCover_subset_intersection X U V K L b⟩)

/-- Canonical refinement to the binary small singular set at `K`. -/
def smallSupportToLeft :
    (smallSupportSubcomplex X U V K L : SSet) ⟶
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X U Kᶜ : SSet) :=
  SSet.Subcomplex.homOfLE (smallSupportSubcomplex_le_left X U V K L)

/-- Canonical refinement to the binary small singular set at `L`. -/
def smallSupportToRight :
    (smallSupportSubcomplex X U V K L : SSet) ⟶
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X V Lᶜ : SSet) :=
  SSet.Subcomplex.homOfLE (smallSupportSubcomplex_le_right X U V K L)

/-- Canonical refinement to the binary small singular set at the intersection support. -/
def smallSupportToIntersection :
    (smallSupportSubcomplex X U V K L : SSet) ⟶
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∩ V) (K ∩ L)ᶜ : SSet) :=
  SSet.Subcomplex.homOfLE (smallSupportSubcomplex_le_intersection X U V K L)

@[reassoc (attr := simp)]
theorem smallSupportToLeft_inclusion :
    smallSupportToLeft X U V K L ≫ (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X U Kᶜ).ι =
      DeRham.Comparison.SmallSingularSet.smallSingularInclusion X (smallSupportCover X U V K L) := rfl

@[reassoc (attr := simp)]
theorem smallSupportToRight_inclusion :
    smallSupportToRight X U V K L ≫ (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X V Lᶜ).ι =
      DeRham.Comparison.SmallSingularSet.smallSingularInclusion X (smallSupportCover X U V K L) := rfl

@[reassoc (attr := simp)]
theorem smallSupportToIntersection_inclusion :
    smallSupportToIntersection X U V K L ≫
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∩ V) (K ∩ L)ᶜ).ι =
      DeRham.Comparison.SmallSingularSet.smallSingularInclusion X (smallSupportCover X U V K L) := rfl

end Cover

section ScalarChains

variable (R : Type) [CommRing R] (X : TopCat.{0}) (U V K L : Set X)

/-- Actual scalar chains on the simultaneous small singular subcomplex. -/
abbrev smallSupportScalarChains : ChainComplex (ModuleCat.{0} R) ℕ :=
  Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) (smallSupportSubcomplex X U V K L : SSet)

/-- The canonical ambient inclusion of simultaneous small scalar chains. -/
abbrev smallSupportChainInclusion :
    smallSupportScalarChains R X U V K L ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) X :=
  Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R)
    (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X (smallSupportCover X U V K L))

/-- Refinement to binary small scalar chains at the first support. -/
def smallSupportChainToLeft :
    smallSupportScalarChains R X U V K L ⟶
      Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X U Kᶜ : SSet) :=
  Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) (smallSupportToLeft X U V K L)

/-- Refinement to binary small scalar chains at the second support. -/
def smallSupportChainToRight :
    smallSupportScalarChains R X U V K L ⟶
      Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X V Lᶜ : SSet) :=
  Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) (smallSupportToRight X U V K L)

/-- Refinement to binary small scalar chains at the intersection support. -/
def smallSupportChainToIntersection :
    smallSupportScalarChains R X U V K L ⟶
      Cohomology.Singular.ChainDual.simplicialScalarChains (R := R)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∩ V) (K ∩ L)ᶜ : SSet) :=
  Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) (smallSupportToIntersection X U V K L)

@[reassoc (attr := simp)]
theorem smallSupportChainToLeft_inclusion :
    smallSupportChainToLeft R X U V K L ≫
        Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X U Kᶜ).ι =
      smallSupportChainInclusion R X U V K L := by
  change ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _ ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _ =
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _
  rw [← Functor.map_comp, smallSupportToLeft_inclusion]

@[reassoc (attr := simp)]
theorem smallSupportChainToRight_inclusion :
    smallSupportChainToRight R X U V K L ≫
        Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X V Lᶜ).ι =
      smallSupportChainInclusion R X U V K L := by
  change ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _ ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _ =
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _
  rw [← Functor.map_comp, smallSupportToRight_inclusion]

@[reassoc (attr := simp)]
theorem smallSupportChainToIntersection_inclusion :
    smallSupportChainToIntersection R X U V K L ≫
        Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∩ V) (K ∩ L)ᶜ).ι =
      smallSupportChainInclusion R X U V K L := by
  change ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _ ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _ =
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _
  rw [← Functor.map_comp, smallSupportToIntersection_inclusion]

end ScalarChains

section IntegralChains

variable (X : TopCat.{0}) (U V K L : Set X)

/-- The scalar refinement at `ℤ` commutes with the existing binary integral inclusion. -/
@[reassoc (attr := simp)]
theorem smallSupportChainToLeft_integral_inclusion :
    smallSupportChainToLeft ℤ X U V K L ≫ AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U Kᶜ =
      AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (smallSupportCover X U V K L) := by
  rw [AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
  exact smallSupportChainToLeft_inclusion ℤ X U V K L

@[reassoc (attr := simp)]
theorem smallSupportChainToRight_integral_inclusion :
    smallSupportChainToRight ℤ X U V K L ≫ AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X V Lᶜ =
      AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (smallSupportCover X U V K L) := by
  rw [AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
  exact smallSupportChainToRight_inclusion ℤ X U V K L

@[reassoc (attr := simp)]
theorem smallSupportChainToIntersection_integral_inclusion :
    smallSupportChainToIntersection ℤ X U V K L ≫
        AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∩ V) (K ∩ L)ᶜ =
      AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (smallSupportCover X U V K L) := by
  rw [AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
  exact smallSupportChainToIntersection_inclusion ℤ X U V K L

end IntegralChains

variable (X : TopCat.{0}) (U V K L : Set X)
variable (hU : IsOpen U) (hV : IsOpen V) (hK : IsClosed K) (hL : IsClosed L)
variable (hKU : K ⊆ U) (hLV : L ⊆ V)

/-- The existing support-controlled smallification, applied to the simultaneous
four-cover. Its single output refines to all three required binary small complexes. -/
def smallSupportSmallification :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X ⟶ smallSupportScalarChains ℤ X U V K L :=
  AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationChainMap X (smallSupportCover X U V K L)
    (smallSupportCover_isOpen X U V K L hU hV hK hL)
    (smallSupportCover_covers X U V K L hKU hLV)

/-- The ambient image is exactly the already constructed supported correction
endomorphism for this same four-cover. -/
@[reassoc (attr := simp)]
theorem smallSupportSmallification_inclusion :
    smallSupportSmallification X U V K L hU hV hK hL hKU hLV ≫
        smallSupportChainInclusion ℤ X U V K L =
      AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationEndomorphism X (smallSupportCover X U V K L)
        (smallSupportCover_isOpen X U V K L hU hV hK hL)
        (smallSupportCover_covers X U V K L hKU hLV) :=
  AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationChainMap_inclusion X (smallSupportCover X U V K L)
    (smallSupportCover_isOpen X U V K L hU hV hK hL)
    (smallSupportCover_covers X U V K L hKU hLV)

/-- The actual ambient chain homotopy from the identity to simultaneous smallification. -/
def smallSupportSmallificationHomotopy :
    Homotopy (𝟙 (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X))
      (smallSupportSmallification X U V K L hU hV hK hL hKU hLV ≫
        smallSupportChainInclusion ℤ X U V K L) :=
  AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles.smallificationAmbientHomotopy X (smallSupportCover X U V K L)
    (smallSupportCover_isOpen X U V K L hU hV hK hL)
    (smallSupportCover_covers X U V K L hKU hLV)

/-- The genuine integral small-chain homotopy equivalence for the four-cover. -/
def smallSupportIntegralHomotopyEquiv :
    HomotopyEquiv (smallSupportScalarChains ℤ X U V K L) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) :=
  AlgebraicGeometry.CycleClass.Geometric.ControlledSmallEquivalence.Cycles.controlledSmallChainHomotopyEquiv X (smallSupportCover X U V K L)
    (smallSupportCover_isOpen X U V K L hU hV hK hL)
    (smallSupportCover_covers X U V K L hKU hLV)

@[simp]
theorem smallSupportIntegralHomotopyEquiv_hom :
    (smallSupportIntegralHomotopyEquiv X U V K L hU hV hK hL hKU hLV).hom =
      smallSupportChainInclusion ℤ X U V K L := rfl

@[simp]
theorem smallSupportIntegralHomotopyEquiv_inv :
    (smallSupportIntegralHomotopyEquiv X U V K L hU hV hK hL hKU hLV).inv =
      smallSupportSmallification X U V K L hU hV hK hL hKU hLV := rfl

end

/-!
# The union refinement of simultaneous support-small chains

The same four-cover for two supports also refines the binary cover
`{U ∪ V, (K ∪ L)ᶜ}`. The refinement leaves every ambient singular simplex
unchanged, so the induced scalar-chain maps commute with ambient inclusion.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

section Simplices

variable (X : TopCat.{0}) (U V K L : Set X)

/-- Boolean conjunction gives the cover-index map to the union-support cover. -/
theorem smallSupportCover_subset_union (b : Bool × Bool) :
    smallSupportCover X U V K L b ⊆ if b.1 && b.2 then (K ∪ L)ᶜ else U ∪ V := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c
  · intro x hx
    exact Or.inl hx.1
  · intro x hx
    exact Or.inl hx.1
  · intro x hx
    exact Or.inr hx.2
  · intro x hx hKL
    exact hKL.elim hx.1 hx.2

/-- The simultaneous small singular set lies in the binary union-support one. -/
theorem smallSupportSubcomplex_le_union :
    smallSupportSubcomplex X U V K L ≤
      AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∪ V) (K ∪ L)ᶜ := by
  rw [AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex_eq]
  exact DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex_le_of_refinement X (smallSupportCover X U V K L)
    (fun b : Bool => if b then (K ∪ L)ᶜ else U ∪ V)
    (fun b => ⟨b.1 && b.2, smallSupportCover_subset_union X U V K L b⟩)

/-- The canonical actual simplicial refinement to the union-support cover. -/
def smallSupportToUnion :
    (smallSupportSubcomplex X U V K L : SSet) ⟶
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∪ V) (K ∪ L)ᶜ : SSet) :=
  SSet.Subcomplex.homOfLE (smallSupportSubcomplex_le_union X U V K L)

/-- The refinement retains exactly the original ambient singular simplex. -/
@[reassoc (attr := simp)]
theorem smallSupportToUnion_inclusion :
    smallSupportToUnion X U V K L ≫
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∪ V) (K ∪ L)ᶜ).ι =
      DeRham.Comparison.SmallSingularSet.smallSingularInclusion X (smallSupportCover X U V K L) := rfl

end Simplices

section ScalarChains

variable (R : Type) [CommRing R] (X : TopCat.{0}) (U V K L : Set X)

/-- The actual scalar-chain refinement to the binary union-support model. -/
def smallSupportChainToUnion :
    smallSupportScalarChains R X U V K L ⟶
      Cohomology.Singular.ChainDual.simplicialScalarChains (R := R)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∪ V) (K ∪ L)ᶜ : SSet) :=
  Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) (smallSupportToUnion X U V K L)

/-- The scalar-chain refinement commutes exactly with actual ambient inclusion. -/
@[reassoc (attr := simp)]
theorem smallSupportChainToUnion_inclusion :
    smallSupportChainToUnion R X U V K L ≫
        Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X (U ∪ V) (K ∪ L)ᶜ).ι =
      smallSupportChainInclusion R X U V K L := by
  change ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _ ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _ =
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map _
  rw [← Functor.map_comp, smallSupportToUnion_inclusion]

end ScalarChains

/-- The integral specialization agrees with the existing binary integral inclusion. -/
@[reassoc (attr := simp)]
theorem smallSupportChainToUnion_integral_inclusion
    (X : TopCat.{0}) (U V K L : Set X) :
    smallSupportChainToUnion ℤ X U V K L ≫
        AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∪ V) (K ∪ L)ᶜ =
      AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (smallSupportCover X U V K L) := by
  rw [AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
  exact smallSupportChainToUnion_inclusion ℤ X U V K L

end

end OAI.AlgebraicTopology.Duality.Poincare.SmallSupportCover
