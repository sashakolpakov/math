import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallProductComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorDescent
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.QuotientHomotopy
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductHomotopySupport
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Relative Cross Nonvanishing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions

noncomputable section

section

/-!
# DegreeTwo: the relative cross product has an actual left inverse

The canonical cross–Alexander–Whitney homotopy descends through the two
factor quotients. Thus the relative cross product is injective on homology;
this is the needed nonvanishing statement for local product generators.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y)

theorem smallCrossWhitney_projection :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B) ≫
      (SmallProductComparison.Constructions.smallRelativeChainCross X Y A B ≫ SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) =
    (RelativeCrossSupport.Constructions.singularChainCross ℚ X Y ≫ AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw ℚ (X,Y)) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B) := by
  rw [← Category.assoc, SmallProductComparison.Constructions.smallRelativeChainCross_projection, Category.assoc,
    SmallProductComparison.Constructions.smallRelativeAlexanderWhitney_projection, RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre, Category.assoc]

def smallCrossWhitneyHomotopy :
    Homotopy (SmallProductComparison.Constructions.smallRelativeChainCross X Y A B ≫ SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B)
      (𝟙 (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B)) := by
  let π := CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B
  let H := ProductHomotopySupport.Constructions.crossAlexanderWhitneyHomotopy ℚ X Y
  have : ∀ n, Epi (π.f n) := fun n => TensorChainQuotient.Constructions.tensorChainHom_degree_epi _ _ n
  refine QuotientHomotopy.Constructions.quotientHomotopyOfComponents π π (smallCrossWhitney_projection X Y A B)
    (by simp) H
    (fun a b => TensorDescent.Constructions.tensorDegreeQuotientDesc
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ Y B)
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ Y B)
      a (H.hom a b ≫ π.f b)
      (ProductHomotopySupport.Constructions.crossAlexanderWhitneyHomotopy_left_zero ℚ X Y A B a b)
      (ProductHomotopySupport.Constructions.crossAlexanderWhitneyHomotopy_right_zero ℚ X Y A B a b)) ?_
  intro a b
  exact TensorDescent.Constructions.tensorDegreeQuotientDesc_fac
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ Y B)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ Y B)
    a (H.hom a b ≫ π.f b)
    (ProductHomotopySupport.Constructions.crossAlexanderWhitneyHomotopy_left_zero ℚ X Y A B a b)
    (ProductHomotopySupport.Constructions.crossAlexanderWhitneyHomotopy_right_zero ℚ X Y A B a b)

theorem smallCrossWhitney_homology (n : ℕ) :
    HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeChainCross X Y A B) n ≫
      HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) n = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp,
    (smallCrossWhitneyHomotopy X Y A B).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

theorem relativeCrossWhitney_homology (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n ≫
      SmallProductComparison.Constructions.relativeAlexanderWhitneyHomology X Y A B hA hB n = 𝟙 _ := by
  let e := RationalSmallDescent.Constructions.binaryRationalComplementHomologyIso (TopCat.of (X × Y))
    (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) (hA.preimage continuous_fst) (hB.preimage continuous_snd) n
  have hc : HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeChainCross X Y A B) n ≫ e.hom =
      RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n := by
    change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
    rw [← HomologicalComplex.homologyMap_comp, SmallProductComparison.Constructions.smallRelativeChainCross_to_relative]
    rfl
  change RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n ≫
    (e.inv ≫ HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) n) = _
  rw [← hc, Category.assoc, Iso.hom_inv_id_assoc]
  exact smallCrossWhitney_homology X Y A B n

theorem relativeSingularCrossHomology_injective (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    Function.Injective (RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n) := by
  have h := relativeCrossWhitney_homology X Y A B hA hB n
  have hi : Function.LeftInverse (SmallProductComparison.Constructions.relativeAlexanderWhitneyHomology X Y A B hA hB n)
      (RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n) := fun z => ConcreteCategory.congr_hom h z
  exact hi.injective

end

/-!
# DegreeTwo: nonvanishing of actual relative cross products

The algebraic tensor homology decomposition and the proved left inverse
show that two nonzero relative classes have nonzero cross product over ℚ.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology
open scoped TensorProduct DirectSum

private theorem rational_tmul_ne_zero
    {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℚ V] [Module ℚ W]
    {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[ℚ] w ≠ 0 := by
  obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_eq_one ℚ hv
  obtain ⟨ψ,hψ⟩ := Module.Projective.exists_dual_eq_one ℚ hw
  intro h
  have h' := congrArg (fun z => TensorProduct.lid ℚ ℚ (TensorProduct.map φ ψ z)) h
  have h10 : (1 : ℚ) = 0 := by
    simpa only [TensorProduct.map_tmul, TensorProduct.lid_tmul, hφ, hψ, one_smul, map_zero]
      using h'
  exact one_ne_zero h10

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (p q : ℕ)

def relativeHomologyCrossClass
    (a : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p) (b : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X × Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p + q) :=
  RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B (p + q)
    (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) (p + q)
      (DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
        (fun ij => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A ij.val.1 ⊗[ℚ]
          CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B ij.val.2) ⟨(p,q),rfl⟩ (a ⊗ₜ[ℚ] b)))

theorem relativeHomologyCrossClass_ne_zero (hA : IsOpen A) (hB : IsOpen B)
    {a : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p} {b : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q}
    (ha : a ≠ 0) (hb : b ≠ 0) : relativeHomologyCrossClass X Y A B p q a b ≠ 0 := by
  classical
  intro hz
  let e := AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) (p + q)
  let z := DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
    (fun ij => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A ij.val.1 ⊗[ℚ]
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B ij.val.2) ⟨(p,q),rfl⟩ (a ⊗ₜ[ℚ] b)
  have hz' : e z = 0 := by
    apply relativeSingularCrossHomology_injective X Y A B hA hB (p + q)
    exact hz.trans (map_zero _).symm
  have hz'' : z = 0 := e.injective (hz'.trans e.map_zero.symm)
  have h := congrArg (DirectSum.component ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
    (fun ij => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A ij.val.1 ⊗[ℚ]
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B ij.val.2) ⟨(p,q),rfl⟩) hz''
  dsimp only [z] at h
  rw [DirectSum.component.lof_self, map_zero] at h
  exact rational_tmul_ne_zero ha hb h

theorem crossSupportComplement_punctures (x : X) (y : Y) :
    RelativeCrossSupport.Constructions.crossSupportComplement X Y ({x}ᶜ) ({y}ᶜ) = ({(x,y)}ᶜ : Set (X × Y)) := by
  ext z
  simp only [RelativeCrossSupport.Constructions.crossSupportComplement, Set.mem_union, Set.mem_preimage, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  change z.1 ≠ x ∨ z.2 ≠ y ↔ z ≠ (x,y)
  constructor
  · rintro (hx | hy) h
    · exact hx (congrArg Prod.fst h)
    · exact hy (congrArg Prod.snd h)
  · intro h
    by_cases hx : z.1 = x
    · exact Or.inr (fun hy => h (Prod.ext hx hy))
    · exact Or.inl hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions
