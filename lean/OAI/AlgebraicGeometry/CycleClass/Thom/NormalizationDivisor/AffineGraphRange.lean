import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range

/-! # Affine Graph Range -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphRange.Constructions

noncomputable section

/-! The lifted normalization divisor graph has exactly the full divisor-support graph in the affine source over the retained ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range.Constructions.BranchRange OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

def affinePrimeSet : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a ⁻¹' Set.range (Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))

variable [IsAffine X.left] {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

def affineFullGraph (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : V.analyticSpace × (Fin d → ℂ) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y), Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y)

variable (U : Opens V.analyticSpace)
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

def affinePrimeGraphImage : Set (U × (Fin d → ℂ)) :=
  {u | ∃ y, y ∈ affinePrimeSet V W z a ∧ affineFullGraph V W a f y = (u.1.val, u.2)}

omit [IsAffine X.left] in
theorem coverAffineLift_ambient (x : AffineCoordinates.Constructions.coverSource V W z U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a (AffineCoordinates.Constructions.coverAffineLift V W z U a hcover x)) =
      EtaleGraphOpenImmersion.Constructions.etaleBase (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) x.val :=
  (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W)) (AffineCoordinates.Constructions.coverAffineLift_commutes V W z U a hcover x)).trans
    (congrFun (AffineCoordinates.Constructions.cover_liftBase_eq V W z) x.val)

theorem coverAffineGraph_range (hU : (U : Set V.analyticSpace) ⊆ GraphOpen.Constructions.goodAmbient V W z) :
    Set.range (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U
      (AffineCoordinates.Constructions.coverAffineCoordinates V W z U a hcover f)) = affinePrimeGraphImage V W z a f U := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨AffineCoordinates.Constructions.coverAffineLift V W z U a hcover x, ?_, ?_⟩
    · exact (congrArg (fun y => y ∈ Set.range (Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
          (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))) (AffineCoordinates.Constructions.coverAffineLift_commutes V W z U a hcover x)).mpr
        (Range.Constructions.BranchRange.sourceAmbientMap_range_subset_prime V W z ⟨x.val, rfl⟩)
    · exact Prod.ext (coverAffineLift_ambient V W z a U hcover x) rfl
  · rintro ⟨y, hy, he⟩
    have he1 := congrArg (Prod.fst : V.analyticSpace × (Fin d → ℂ) → V.analyticSpace) he
    have hyU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U :=
      (congrArg (fun v : V.analyticSpace => v ∈ U) he1).mpr u.1.property
    obtain ⟨l, hl⟩ := Range.Constructions.BranchRange.fullPrime_point_mem_cover_range V W z (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) hy (hU hyU)
    have hb : EtaleGraphOpenImmersion.Constructions.etaleBase (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) l =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) :=
      (congrFun (AffineCoordinates.Constructions.cover_liftBase_eq V W z) l).symm.trans
        (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W)) hl)
    have hlU := (congrArg (fun v : V.analyticSpace => v ∈ U) hb).mpr hyU
    let x : AffineCoordinates.Constructions.coverSource V W z U := ⟨l, hlU⟩
    have hxy : AffineCoordinates.Constructions.coverAffineLift V W z U a hcover x = y :=
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion a).injective
        ((AffineCoordinates.Constructions.coverAffineLift_commutes V W z U a hcover x).trans hl)
    refine ⟨x, Prod.ext (Subtype.ext (hb.trans he1)) ?_⟩
    exact (congrArg (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) hxy).trans
      (congrArg (Prod.snd : V.analyticSpace × (Fin d → ℂ) → (Fin d → ℂ)) he)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphRange.Constructions
