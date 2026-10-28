import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionParentClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionCommonBoundary
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.FiberMeeting
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.ChartBounds

/-! # Section Neighborhood -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SectionNeighborhood.BundleCycles

noncomputable section

section

/-! On an actual affine inverse-image chart, the full supported section formula follows from the single global principal boundary. Fiber coverage and all local divisor good-open conditions are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (B : N.left.Opens)
  [Nonempty B] [Nonempty (k.left ⁻¹ᵁ B)] [IsAffine (OpenChart.BundleCycles.finiteAffineBase B).left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

local instance finiteAffineSectionParentNoetherian : AlgebraicGeometry.IsNoetherian ((OpenChart.BundleCycles.finiteAffineSource k B)).left :=
  Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian ((OpenChart.BundleCycles.finiteAffineSourceInclusion k B)).left
local instance finiteAffineSectionParentTopNonempty : Nonempty (⊤ : ((OpenChart.BundleCycles.finiteAffineSource k B)).left.Opens) :=
  ⟨⟨genericPoint ((OpenChart.BundleCycles.finiteAffineSource k B)).left, Opens.mem_top _⟩⟩

variable (s : Γ(((OpenChart.BundleCycles.finiteAffineBase B)).left, ⊤)) (hsn : ((OpenChart.BundleCycles.finiteAffineSource k B)).left.germToFunctionField ⊤ (((OpenChart.BundleCycles.finiteAffineMap k B)).left.appTop s) ≠ 0)

variable (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B)))
  (hgood : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Finite.PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (Finite.ParentSection.BundleCycles.finiteParentRationalFunction (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) (Scheme.germToFunctionField (Over.left (OpenChart.BundleCycles.finiteAffineSource k B)) ⊤ (Scheme.Hom.appTop (Over.Hom.left (OpenChart.BundleCycles.finiteAffineMap k B)) s))) k)

variable (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(((OpenChart.BundleCycles.finiteAffineSource k B)).left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap (OpenChart.BundleCycles.finiteAffineMap k B) f).left]
  (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) y) ∈ U → CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)
  (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

include hf hK hb hgood hsn in
theorem finiteAffine_sectionCup_eq_parentPrincipalClass :
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) (Finite.SectionSupport.BundleCycles.finiteBaseSectionImage (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ s) (Finite.BaseImageClass.BundleCycles.finiteBaseImage_openComplement k U)
      (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (OpenChart.BundleCycles.finiteAffineBase B) s) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (OpenChart.BundleCycles.finiteAffineBase B) s))
      p 1 ((k.left.residueDegree (genericPoint S.left) : ℚ) • Finite.BaseImageClass.BundleCycles.finiteBaseImageCycleClass k p hp U)
      (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ s) =
    LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap N U (Set.range (Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) ∩ Set.range (Finite.SectionSupport.BundleCycles.finiteBaseSectionImage (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ s)) n (p + 1) hn
      (LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRestrictCycle N U (Set.range (Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) ∩ Set.range (Finite.SectionSupport.BundleCycles.finiteBaseSectionImage (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ s)) n (Finite.ParentSection.BundleCycles.finiteParentPrincipalCycle k (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) n (Scheme.germToFunctionField (Over.left (OpenChart.BundleCycles.finiteAffineSource k B)) ⊤ (Scheme.Hom.appTop (Over.Hom.left (OpenChart.BundleCycles.finiteAffineMap k B)) s)))) := by
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OpenChart.BundleCycles.finiteAffineSource k B)) := (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf).isEmbedding.metrizableSpace
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OpenChart.BundleCycles.finiteAffineBase B)) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (OpenChart.BundleCycles.finiteAffineBaseInclusion B)).isEmbedding.metrizableSpace
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget (OpenChart.BundleCycles.finiteAffineBase B) d)) :=
    (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph (OpenChart.BundleCycles.finiteAffineBase B) d).isEmbedding.metrizableSpace
  exact Finite.SectionParentClass.BundleCycles.finiteCycle_sectionCup_eq_parentPrincipalClass k p hp (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) (OpenChart.BundleCycles.finiteAffineMap k B) (OpenChart.BundleCycles.finiteAffineBaseInclusion B) (OpenChart.BundleCycles.finiteAffineChart_square k B)
    d f hf U hUJ (OpenChart.BundleCycles.finiteAffineChart_covers_fibers k B U hUJ) s hsn
    (fun z => hgood.trans (Finite.SectionCommonBoundary.BundleCycles.finitePrincipalCommonOpen_subset_sectionDivisor k (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) (((OpenChart.BundleCycles.finiteAffineMap k B)).left.appTop s) hsn z))
    K hK hb n hn (FiberMeeting.BundleCycles.finiteAffineChart_covers_meeting_supports k B U hUJ n)

end

/-! Every point in the actual common open has (finiteAffineSourceInclusion k B) section-formula neighborhood. The polynomial graph, compact bound, fiber cover, and divisor regularity are all constructed internally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (B : N.left.Opens)
  [Nonempty B] [Nonempty (k.left ⁻¹ᵁ B)] [IsAffine (OpenChart.BundleCycles.finiteAffineBase B).left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

local instance finiteSectionNeighborhoodNoetherian : AlgebraicGeometry.IsNoetherian ((OpenChart.BundleCycles.finiteAffineSource k B)).left :=
  Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian ((OpenChart.BundleCycles.finiteAffineSourceInclusion k B)).left
local instance finiteSectionNeighborhoodTopNonempty : Nonempty (⊤ : ((OpenChart.BundleCycles.finiteAffineSource k B)).left.Opens) :=
  ⟨⟨genericPoint ((OpenChart.BundleCycles.finiteAffineSource k B)).left, Opens.mem_top _⟩⟩

variable (s : Γ(((OpenChart.BundleCycles.finiteAffineBase B)).left, ⊤)) (hsn : ((OpenChart.BundleCycles.finiteAffineSource k B)).left.germToFunctionField ⊤ (((OpenChart.BundleCycles.finiteAffineMap k B)).left.appTop s) ≠ 0)

variable (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

include hsn in
theorem finiteAffine_exists_section_principal_neighborhood (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OpenChart.BundleCycles.finiteAffineBase B))
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B) x ∈ Finite.PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (Finite.ParentSection.BundleCycles.finiteParentRationalFunction (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) (Scheme.germToFunctionField (Over.left (OpenChart.BundleCycles.finiteAffineSource k B)) ⊤ (Scheme.Hom.appTop (Over.Hom.left (OpenChart.BundleCycles.finiteAffineMap k B)) s))) k) :
    ∃ (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
      (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B))),
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B) x ∈ U ∧
      (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Finite.PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (Finite.ParentSection.BundleCycles.finiteParentRationalFunction (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) (Scheme.germToFunctionField (Over.left (OpenChart.BundleCycles.finiteAffineSource k B)) ⊤ (Scheme.Hom.appTop (Over.Hom.left (OpenChart.BundleCycles.finiteAffineMap k B)) s))) k ∧
      CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) (Finite.SectionSupport.BundleCycles.finiteBaseSectionImage (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ s) (Finite.BaseImageClass.BundleCycles.finiteBaseImage_openComplement k U)
        (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (OpenChart.BundleCycles.finiteAffineBase B) s) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (OpenChart.BundleCycles.finiteAffineBase B) s))
        p 1 ((k.left.residueDegree (genericPoint S.left) : ℚ) • Finite.BaseImageClass.BundleCycles.finiteBaseImageCycleClass k p hp U)
        (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ s) =
      LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap N U (Set.range (Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) ∩ Set.range (Finite.SectionSupport.BundleCycles.finiteBaseSectionImage (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ s)) n (p + 1) hn
        (LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRestrictCycle N U (Set.range (Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) ∩ Set.range (Finite.SectionSupport.BundleCycles.finiteBaseSectionImage (OpenChart.BundleCycles.finiteAffineBaseInclusion B) U hUJ s)) n
          (Finite.ParentSection.BundleCycles.finiteParentPrincipalCycle k (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) n (Scheme.germToFunctionField (Over.left (OpenChart.BundleCycles.finiteAffineSource k B)) ⊤ (Scheme.Hom.appTop (Over.Hom.left (OpenChart.BundleCycles.finiteAffineMap k B)) s)))) := by
  obtain ⟨d, f, U₀, K, hf, hclosed, hx₀, hU₀, hK, hb⟩ := ChartBounds.BundleCycles.finiteAffineChart_exists_bounded_graph k B x
  let : IsClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap (OpenChart.BundleCycles.finiteAffineMap k B) f).left := hclosed
  let U := U₀ ⊓ Finite.PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (Finite.ParentSection.BundleCycles.finiteParentRationalFunction (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) (Scheme.germToFunctionField (Over.left (OpenChart.BundleCycles.finiteAffineSource k B)) ⊤ (Scheme.Hom.appTop (Over.Hom.left (OpenChart.BundleCycles.finiteAffineMap k B)) s))) k
  have hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B)) := fun _ hz => hU₀ hz.1
  refine ⟨U, hUJ, ⟨hx₀, hx⟩, (fun _ hz => hz.2), ?_⟩
  exact finiteAffine_sectionCup_eq_parentPrincipalClass k B p hp s hsn U hUJ (fun _ hz => hz.2)
    d f hf K hK (fun y hy => hb y hy.1) n hn

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SectionNeighborhood.BundleCycles
