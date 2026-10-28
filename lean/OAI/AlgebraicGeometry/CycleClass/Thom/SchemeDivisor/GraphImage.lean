import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion

/-! # Graph Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions

noncomputable section

section

/-! The actual regular divisor image in a polynomial graph ambient becomes the literal graph of the original regular divisor parametrization in the ambient product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev graphTarget (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine Y.left] (d : ℕ) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin d) ℂ)

variable {X Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
  [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral N.left] [Smooth N.hom]
  (j : Y ⟶ N) [IsOpenImmersion j.left] (d : ℕ) (g : X ⟶ Y)
  (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d))]
  (z : {x : X.left // Order.coheight x = 1}) (q : ℕ)
  (hq : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + q =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (graphTarget Y d).hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hR : ((Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)) ⁻¹'
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageImmersion.Constructions.regularDivisorMap (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z))) =
    (Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)) ⁻¹'
      (Gysin.Constructions.divisorImageOpen (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)))ᶜ)

theorem divisorOpenImmersion_graphImage :
    Set.range (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU ∘
      (OpenImmersion.Constructions.divisorOpenImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z q hq (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) hR).regularComplementInclusion) =
    Set.range (GraphBaseRestriction.Constructions.restrictedGraph (IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphBase j g (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z)))
      (IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphCoordinates d f (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z))) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))) := by
  let r := Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z)
  let Z := OpenImmersion.Constructions.divisorOpenImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z q hq (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) hR
  have hm : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageImmersion.Constructions.regularDivisorMap (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z) =
      IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphParametrization d g f r := by
    funext x
    exact ImageImmersion.Constructions.regularDivisorMap_apply (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z x
  have hr : Set.range Z.regularComplementInclusion =
      (Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)) ⁻¹'
        Set.range (IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphParametrization d g f r) :=
    ((OpenImmersion.Constructions.divisorOpenImmersion_range (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z q hq (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) hR).trans hR.symm).trans
      (congrArg (fun k : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d) =>
        (Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)) ⁻¹' Set.range k) hm)
  exact (Set.range_comp (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU) Z.regularComplementInclusion).trans
    ((congrArg (fun S => IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU '' S) hr).trans
      ((IntrinsicGraphImageRestriction.Constructions.Intrinsic.restrictedGraphImage_range_eq_image j d U hU g f r).symm.trans
        (IntrinsicGraphImageRestriction.Constructions.Intrinsic.restrictedGraphImage_range j d U hU g f r)))

end

/-! The actual divisor immersion in a polynomial graph ambient has the full divisor-support graph as its image in the product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
  [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral N.left] [Smooth N.hom]
  (j : Y ⟶ N) [IsOpenImmersion j.left] (d : ℕ) (g : X ⟶ Y)
  (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d))]
  (z : {x : X.left // Order.coheight x = 1}) (q : ℕ)
  (hq : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + q =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (graphTarget Y d).hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hR : ((Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)) ⁻¹'
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageImmersion.Constructions.regularDivisorMap (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z))) =
    (Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)) ⁻¹'
      (Gysin.Constructions.divisorImageOpen (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)))ᶜ)

theorem divisorOpenImmersion_fullGraphImage :
    Set.range (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU ∘
      (OpenImmersion.Constructions.divisorOpenImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z q hq (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) hR).regularComplementInclusion) =
    Set.range (GraphBaseRestriction.Constructions.restrictedGraph (IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphBase j g (Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z)))
      (IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphCoordinates d f (Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z))) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))) := by
  let r := Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z)
  let Z := OpenImmersion.Constructions.divisorOpenImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z q hq (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) hR
  have hr : Set.range Z.regularComplementInclusion =
      (Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphTarget Y d)) ⁻¹'
        Set.range (IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphParametrization d g f r) := by
    apply (OpenImmersion.Constructions.divisorOpenImmersion_range (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z q hq (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) hR).trans
    ext v
    exact not_not
  exact (Set.range_comp (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU) Z.regularComplementInclusion).trans
    ((congrArg (fun S => IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU '' S) hr).trans
      ((IntrinsicGraphImageRestriction.Constructions.Intrinsic.restrictedGraphImage_range_eq_image j d U hU g f r).symm.trans
        (IntrinsicGraphImageRestriction.Constructions.Intrinsic.restrictedGraphImage_range j d U hU g f r)))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions
