import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeRegular
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage

/-! # Divisor Regular Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorRegularImage.Constructions

noncomputable section

/-! On the constructed normalization-divisor good open, the actual divisor image in the affine polynomial graph ambient equals its regular image. This supplies the geometric input for the divisor Gysin–Thom comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeRegular.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (hs : a ≫ Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  (z : {x : X.left // Order.coheight x = 1}) (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a z))

include hs hU in
omit [IsIntegral X.left] [IsOpenImmersion j.left] in
theorem affineDivisorGraph_regularImage :
    ((Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) ⁻¹'
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeDivisor.ImageImmersion.Constructions.regularDivisorMap (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z))) =
    (Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) ⁻¹'
      (SchemeDivisor.Gysin.Constructions.divisorImageOpen (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)))ᶜ := by
  ext v
  constructor
  · rintro ⟨r, hr⟩
    change v.val ∉ SchemeDivisor.Gysin.Constructions.divisorImageOpen (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z
    rw [← hr, SchemeDivisor.ImageImmersion.Constructions.regularDivisorMap_apply]
    exact (SchemeDivisor.Gysin.Constructions.divisorImage_mem_iff (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z _).mpr
      (Scheme.RegularSupport.Constructions.regularInclusion_subset X (SchemeDivisor.Purity.Constructions.primeSupport X z) ⟨r, rfl⟩)
  · intro hv
    have himg : v.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ∘
        Scheme.RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) := Classical.not_not.mp hv
    obtain ⟨t, ht⟩ := himg
    let x := Scheme.RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z) t
    have hxA : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x ∈ IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U :=
      (congrArg (fun v => v ∈ IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) ht).mpr v.property
    have hb := (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphPoint_mem_ambientOpen j d U g f x).mp hxA
    have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x) :=
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp a (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) x).symm.trans
        ((congrArg (fun k => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k x) hs).trans (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp g j x))
    have hxg := hU ((congrArg (fun y : V.analyticSpace => y ∈ U) he).mpr hb)
    obtain ⟨r, hr⟩ := PrimeRegular.Constructions.affinePrime_regular_over_goodAmbient V W a z x ⟨t, rfl⟩ hxg
    exact ⟨r, (SchemeDivisor.ImageImmersion.Constructions.regularDivisorMap_apply (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z r).trans
      ((congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f)) hr).trans ht)⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorRegularImage.Constructions
