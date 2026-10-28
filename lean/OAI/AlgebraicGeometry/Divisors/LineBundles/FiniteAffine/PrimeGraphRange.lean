import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphRange
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction

/-! # Prime Graph Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrimeGraphRange.BundleCycles

noncomputable section

/-! The full affine prime graph agrees with the finite ambient prime graph through the actual commuting square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsAffine Y.left] (a : X ⟶ S) [IsOpenImmersion a.left]
  (g : X ⟶ Y) (j : Y ⟶ N) (hs : a ≫ k = g ≫ j)
  (z : {x : X.left // Order.coheight x = 1}) {d : ℕ}
  (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))

include hs in
omit [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left] [IsAffine Y.left] [IsOpenImmersion a.left] in
omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [IsFinite (Over.Hom.left k)] in
theorem finiteAffine_square_point (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp a (k) x).symm.trans
    ((congrArg (fun k => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k x) hs).trans (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp g j x))

include hs in
omit [IsIntegral X.left] [Smooth X.hom] [IsAffine Y.left] in
omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [IsFinite (Over.Hom.left k)] in
theorem finiteAffinePrimeGraphImage_eq_fullSupportGraph : FiniteSupport.AffineGraphRange.BundleCycles.finiteSupportAffineGraphImage k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) a f U =
    Set.range (CycleClass.Thom.GraphBaseRestriction.Constructions.restrictedGraph (CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphBase j g (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)))
      (CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphCoordinates d f (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z))) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))) := by
  ext u
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp (CycleClass.Thom.Open.PrimeSupport.Constructions.primeSupport_analytic_preimage a z) y).mp hy
    have hb : CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphBase j g (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)) t = u.1.val :=
      (congrArg (fun x => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x)) ht).trans
        ((finiteAffine_square_point k a g j hs y).symm.trans
          (congrArg (Prod.fst : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) × (Fin d → ℂ) → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) he))
    have htU := (congrArg (fun v : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) => v ∈ U) hb).mpr u.1.property
    refine ⟨⟨t, htU⟩, Prod.ext (Subtype.ext hb) ?_⟩
    exact (congrArg (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) ht).trans
      (congrArg (Prod.snd : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) × (Fin d → ℂ) → (Fin d → ℂ)) he)
  · rintro ⟨t, rfl⟩
    refine ⟨CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) t.val, ?_, ?_⟩
    · exact (Set.ext_iff.mp (CycleClass.Thom.Open.PrimeSupport.Constructions.primeSupport_analytic_preimage a z) _).mpr ⟨t.val, rfl⟩
    · exact Prod.ext (finiteAffine_square_point k a g j hs _) rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrimeGraphRange.BundleCycles
