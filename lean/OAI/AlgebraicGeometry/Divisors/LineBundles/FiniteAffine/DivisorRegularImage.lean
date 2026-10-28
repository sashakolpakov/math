import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrimeRegular
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage

/-! # Divisor Regular Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorRegularImage.BundleCycles

noncomputable section

/-! On the retained finite-image open, the actual divisor image in the polynomial graph ambient equals its regular image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ S) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ N) [IsOpenImmersion j.left]
  (hs : a ≫ k = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  [IsClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  (z : {x : X.left // Order.coheight x = 1}) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)))

include hs hU in
omit [IsIntegral X.left] [IsOpenImmersion j.left] in
omit [AlgebraicGeometry.IsIntegral S.left] in
theorem finiteAffineDivisorGraph_regularImage :
    ((Subtype.val : CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) ⁻¹'
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions.regularDivisorMap (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z))) =
    (Subtype.val : CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) ⁻¹'
      (CycleClass.Thom.SchemeDivisor.Gysin.Constructions.divisorImageOpen (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d)))ᶜ := by
  ext v
  constructor
  · rintro ⟨r, hr⟩
    change v.val ∉ CycleClass.Thom.SchemeDivisor.Gysin.Constructions.divisorImageOpen (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z
    rw [← hr, CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions.regularDivisorMap_apply]
    exact (CycleClass.Thom.SchemeDivisor.Gysin.Constructions.divisorImage_mem_iff (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z _).mpr
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion_subset X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) ⟨r, rfl⟩)
  · intro hv
    have himg : v.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ∘
        CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)) := Classical.not_not.mp hv
    obtain ⟨t, ht⟩ := himg
    let x := CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) t
    have hxA : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x ∈ CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U :=
      (congrArg (fun v => v ∈ CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) ht).mpr v.property
    have hb := (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphPoint_mem_ambientOpen j d U g f x).mp hxA
    have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x) :=
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp a (k) x).symm.trans
        ((congrArg (fun k => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k x) hs).trans (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp g j x))
    have hxg := hU ((congrArg (fun y : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) => y ∈ U) he).mpr hb)
    obtain ⟨r, hr⟩ := PrimeRegular.BundleCycles.finiteAffinePrime_regular_over_retained k a z x ⟨t, rfl⟩ hxg
    exact ⟨r, (CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions.regularDivisorMap_apply (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z r).trans
      ((congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f)) hr).trans ht)⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorRegularImage.BundleCycles
