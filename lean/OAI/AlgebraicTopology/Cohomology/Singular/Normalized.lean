import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.Smooth
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-! # Normalized -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Normalized

noncomputable section

/-!
# Normalized smooth and continuous singular cochains

Mathlib constructs a genuine homotopy equivalence from simplicial chains to
normalized simplicial chains. Applying that construction with coefficients in
the opposite category of modules yields normalized cochains and a homotopy
equivalence with the ordinary cochains. Their inclusion vanishes on every
degenerate simplex.

This is simplicial normalization. It is not an identification with a cubical
chain or cochain complex; such an identification needs a separate comparison.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

variable {R : Type} [Ring R]

/-- Actual normalized simplicial cochains, by the opposite-category construction. -/
abbrev normalizedSimplicialCochains (K : SSet.{0}) (M : ModuleCat.{0} R) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (K.normalizedChainComplex (op M)).unop

/-- The canonical inclusion of normalized cochains into all cochains. -/
def normalizedCochainInclusion (K : SSet.{0}) (M : ModuleCat.{0} R) :
    normalizedSimplicialCochains K M ⟶ Basic.simplicialCochains K M :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (K.toNormalizedChainComplex (op M)).op

/-- The canonical cochain projection onto normalized cochains. -/
def normalizedCochainProjection (K : SSet.{0}) (M : ModuleCat.{0} R) :
    Basic.simplicialCochains K M ⟶ normalizedSimplicialCochains K M :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (K.fromNormalizedChainComplex (op M)).op

set_option backward.isDefEq.respectTransparency false in
/-- The original simplicial normalization homotopy equivalence, on cochains. -/
def normalizedCochainHomotopyEquiv (K : SSet.{0}) (M : ModuleCat.{0} R) :
    HomotopyEquiv (Basic.simplicialCochains K M) (normalizedSimplicialCochains K M) where
  hom := normalizedCochainProjection K M
  inv := normalizedCochainInclusion K M
  homotopyHomInvId := by
    change Homotopy
      ((HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
          (K.fromNormalizedChainComplex (op M)).op ≫
        (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
          (K.toNormalizedChainComplex (op M)).op)
      (𝟙 ((HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).obj
        (op (K.chainComplex (op M)))))
    simpa only [normalizedCochainProjection, normalizedCochainInclusion,
      SSet.homotopyEquivNormalizedChainComplex_hom,
      SSet.homotopyEquivNormalizedChainComplex_inv,
      op_comp, Functor.map_comp, op_id,
      (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map_id
        (op (K.chainComplex (op M)))] using
      (K.homotopyEquivNormalizedChainComplex (op M)).homotopyHomInvId.unop
  homotopyInvHomId := by
    change Homotopy
      ((HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
          (K.toNormalizedChainComplex (op M)).op ≫
        (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
          (K.fromNormalizedChainComplex (op M)).op)
      (𝟙 ((HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).obj
        (op (K.normalizedChainComplex (op M)))))
    simpa only [normalizedCochainProjection, normalizedCochainInclusion,
      SSet.homotopyEquivNormalizedChainComplex_hom,
      SSet.homotopyEquivNormalizedChainComplex_inv,
      op_comp, Functor.map_comp, op_id,
      (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map_id
        (op (K.normalizedChainComplex (op M)))] using
      (K.homotopyEquivNormalizedChainComplex (op M)).homotopyInvHomId.unop

/-- Passing to normalized cochains preserves the actual cohomology object. -/
def normalizedCohomologyIso (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (Basic.simplicialCochains K M).homology n ≅
      (normalizedSimplicialCochains K M).homology n :=
  (normalizedCochainHomotopyEquiv K M).toHomologyIso n

/-- The included normalized cochains evaluate to zero on a degenerate simplex. -/
theorem normalizedCochainInclusion_evaluation_zero (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (s : K _⦋n⦌) (hs : s ∈ K.degenerate n) :
    (normalizedCochainInclusion K M).f n ≫ Coefficients.simplicialEvaluation K M s = 0 := by
  change ((K.toNormalizedChainComplex (op M)).f n).unop ≫
    (K.ιChainComplex (R := op M) s).unop = 0
  rw [← unop_comp]
  change (K.ιNormalizedChainComplex (R := op M) s).unop = 0
  rw [K.ιNormalizedChainComplex_eq_zero s hs]
  rfl

/-- Elementwise vanishing of normalized cochains on actual degenerate simplices. -/
theorem normalizedCochainInclusion_vanishes (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (s : K _⦋n⦌) (hs : s ∈ K.degenerate n)
    (c : (normalizedSimplicialCochains K M).X n) :
    Coefficients.simplicialEvaluation K M s ((normalizedCochainInclusion K M).f n c) = 0 :=
  ConcreteCategory.congr_hom (normalizedCochainInclusion_evaluation_zero K M s hs) c

/-- Every class can be represented by a cocycle from the actual normalized complex. -/
theorem exists_normalizedCocycle (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ)
    (a : (Basic.simplicialCochains K M).homology n) :
    ∃ c : Representatives.cochainCocycles (normalizedSimplicialCochains K M) n,
      (HomologicalComplex.homologyMap (normalizedCochainInclusion K M) n)
        (Representatives.cochainClass (normalizedSimplicialCochains K M) n c) = a := by
  let e := normalizedCohomologyIso K M n
  obtain ⟨c, hc⟩ := Representatives.cochainClass_surjective (normalizedSimplicialCochains K M) n (e.hom a)
  refine ⟨c, ?_⟩
  rw [hc]
  exact ConcreteCategory.congr_hom e.hom_inv_id a

/-- Every ordinary cohomology class has a cocycle representative vanishing on all
degenerate simplices. This statement uses the actual ordinary cochain complex. -/
theorem exists_degenerateVanishingRepresentative (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n : ℕ) (a : (Basic.simplicialCochains K M).homology n) :
    ∃ c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n,
      Representatives.cochainClass (Basic.simplicialCochains K M) n c = a ∧
      ∀ (s : K _⦋n⦌), s ∈ K.degenerate n → Coefficients.simplicialEvaluation K M s c.val = 0 := by
  obtain ⟨c, hc⟩ := exists_normalizedCocycle K M n a
  refine ⟨RepresentativesNaturality.cochainCocycleMap (normalizedCochainInclusion K M) n c, ?_, ?_⟩
  · exact (RepresentativesNaturality.cochainClass_naturality (normalizedCochainInclusion K M) n c).symm.trans hc
  · intro s hs
    exact normalizedCochainInclusion_vanishes K M s hs c.val

/-- Normalized cochains of the genuine continuous singular simplicial set. -/
abbrev normalizedSingularCochains (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  normalizedSimplicialCochains (TopCat.toSSet.obj X) M

/-- Continuous singular cochains and their normalization are genuinely homotopy equivalent. -/
abbrev normalizedSingularCochainHomotopyEquiv (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    HomotopyEquiv (Basic.singularCochains M X) (normalizedSingularCochains M X) :=
  normalizedCochainHomotopyEquiv (TopCat.toSSet.obj X) M

/-- The induced cohomology isomorphism for continuous singular cochains. -/
abbrev normalizedSingularCohomologyIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology M X n ≅ (normalizedSingularCochains M X).homology n :=
  normalizedCohomologyIso (TopCat.toSSet.obj X) M n

/-- Normalized cochains of the actual smooth-singular simplicial set. -/
abbrev normalizedSmoothSingularCochains (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  normalizedSimplicialCochains (Smooth.smoothSingularSubcomplex E).toSSet M

/-- Smooth singular cochains and their normalization are genuinely homotopy equivalent. -/
abbrev normalizedSmoothSingularCochainHomotopyEquiv (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    HomotopyEquiv (Smooth.smoothSingularCochains M E) (normalizedSmoothSingularCochains M E) :=
  normalizedCochainHomotopyEquiv (Smooth.smoothSingularSubcomplex E).toSSet M

/-- The induced cohomology isomorphism for smooth singular cochains. -/
abbrev normalizedSmoothSingularCohomologyIso (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    (Smooth.smoothSingularCochains M E).homology n ≅
      (normalizedSmoothSingularCochains M E).homology n :=
  normalizedCohomologyIso (Smooth.smoothSingularSubcomplex E).toSSet M n

end

end OAI.AlgebraicTopology.Cohomology.Singular.Normalized
