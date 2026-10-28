import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphRange
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction

/-! # Prime Graph Range -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeGraphRange.Constructions

noncomputable section

/-! The full affine prime-support graph agrees with the normalization prime-support graph through the actual commuting ambient maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphRange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsAffine Y.left] (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  (g : X ⟶ Y) (j : Y ⟶ V.toOver) (hs : a ≫ Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W = g ≫ j)
  (z : {x : X.left // Order.coheight x = 1}) {d : ℕ}
  (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (U : Opens V.analyticSpace)

include hs in
omit [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left] [IsAffine Y.left] [IsOpenImmersion a.left] in
theorem normalization_square_point (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp a (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) x).symm.trans
    ((congrArg (fun k => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k x) hs).trans (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp g j x))

include hs in
omit [IsIntegral X.left] [Smooth X.hom] [IsAffine Y.left] in
theorem affinePrimeGraphImage_eq_fullSupportGraph : NormalizationDivisor.AffineGraphRange.Constructions.affinePrimeGraphImage V W (Open.PrimeSupport.Constructions.ambientPrime a z) a f U =
    Set.range (GraphBaseRestriction.Constructions.restrictedGraph (IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphBase j g (Scheme.RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
      (IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphCoordinates d f (Scheme.RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z))) (U : Set V.analyticSpace)) := by
  ext u
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp (Open.PrimeSupport.Constructions.primeSupport_analytic_preimage a z) y).mp hy
    have hb : IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphBase j g (Scheme.RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) t = u.1.val :=
      (congrArg (fun x => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x)) ht).trans
        ((normalization_square_point V W a g j hs y).symm.trans
          (congrArg (Prod.fst : V.analyticSpace × (Fin d → ℂ) → V.analyticSpace) he))
    have htU := (congrArg (fun v : V.analyticSpace => v ∈ U) hb).mpr u.1.property
    refine ⟨⟨t, htU⟩, Prod.ext (Subtype.ext hb) ?_⟩
    exact (congrArg (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) ht).trans
      (congrArg (Prod.snd : V.analyticSpace × (Fin d → ℂ) → (Fin d → ℂ)) he)
  · rintro ⟨t, rfl⟩
    refine ⟨Scheme.RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z) t.val, ?_, ?_⟩
    · exact (Set.ext_iff.mp (Open.PrimeSupport.Constructions.primeSupport_analytic_preimage a z) _).mpr ⟨t.val, rfl⟩
    · exact Prod.ext (normalization_square_point V W a g j hs _) rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeGraphRange.Constructions
