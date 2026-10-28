import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTensorHomology
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallCoefficientComparison

/-! # Exterior Cup Small Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions

noncomputable section

/-!
# DegreeTwo: the actual supported exterior cup agrees with tensor evaluation

This compares the already constructed two-support cup to the canonical
Alexander–Whitney tensor functional on rationalized integral small cycles.
It retains the actual product projections and both original support sets.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)

def relativeExteriorCup
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y))
      (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p+q) :=
  SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
    (hA.preimage continuous_fst) (hB.preimage continuous_snd) p q
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst : TopCat.of (X×Y) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p a)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodSnd : TopCat.of (X×Y) ⟶ Y)
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q b)

variable (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
variable (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) q)

theorem relativeExteriorCup_small_projection
    (u : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (X × Y))).X (p+q))
    (hu : (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection (TopCat.of (X × Y)) (Prod.fst ⁻¹' A)
      (Prod.snd ⁻¹' B)).f (p+q) u ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains (TopCat.of (X × Y))
        (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)) (p+q)) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y))
      (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p+q)
      (relativeExteriorCup X Y A B hA hB p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d))
      ((RationalSmallDescent.Constructions.binaryRationalComplementHomologyIso (TopCat.of (X × Y))
        (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
        (hA.preimage continuous_fst) (hB.preimage continuous_snd) (p+q)).hom
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (p+q) (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle _ (p+q) 1
          ⟨(CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection _ _ _).f (p+q) u,hu⟩))) =
    RelativeTensorHomology.Constructions.relativeTensorHomologyFunctional X Y A B p q c d
      (HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) (p+q)
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (p+q) (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle _ (p+q) 1
          ⟨(CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection _ _ _).f (p+q) u,hu⟩))) := by
  dsimp only [RelativeCrossSupport.Constructions.crossSupportComplement]
  rw [SmallCoefficientComparison.Constructions.binarySmallCup_scalarEvaluation, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    RelativeTensorHomology.Constructions.relativeTensorHomologyFunctional_class]
  let c' := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst : TopCat.of (X×Y) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx)) p c
  let d' := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (TopCat.prodSnd : TopCat.of (X×Y) ⟶ Y)
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx)) q d
  have hc : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.prodFst : TopCat.of (X×Y) ⟶ X) (A := Prod.fst ⁻¹' A) (B := A)
      (fun _ hx => hx) p (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c' :=
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality _ p c
  have hd : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.prodSnd : TopCat.of (X×Y) ⟶ Y) (A := Prod.snd ⁻¹' B) (B := B)
      (fun _ hx => hx) q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d' :=
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality _ q d
  rw [relativeExteriorCup, hc, hd, SupportCup.Constructions.twoSupportCup_small_projection_cup]
  have hci : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      (Prod.fst ⁻¹' A)).f p c'.val =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst).f p
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c.val) :=
    ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) TopCat.prodFst
        (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx)) p) c.val
  have hdi : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      (Prod.snd ⁻¹' B)).f q d'.val =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd).f q
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y B).f q d.val) :=
    ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) TopCat.prodSnd
        (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx)) q) d.val
  rw [hci,hdi]
  change _ = RelativeTensorFunctional.Constructions.relativeTensorFunctional X Y A B p q c.val d.val
    ((SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B).f (p+q)
      ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection _ _ _).f (p+q) u)))
  rw [← SmallCoefficientComparison.Constructions.binaryRationalComplementProjection_integral,
    RelativeTensorFunctional.Constructions.relativeTensorFunctional_smallAW_projection]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions
