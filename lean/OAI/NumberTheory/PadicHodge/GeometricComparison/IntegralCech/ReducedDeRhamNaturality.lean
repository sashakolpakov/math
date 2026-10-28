import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.QuotientCechRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.RefinementNaturality

/-! # Reduced De Rham Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ReducedDeRhamNaturality.IntegralCechReducedDeRhamNaturality

noncomputable section

/-! Reduction of the original integral de Rham H-one coordinates
preserves actual geometric pullback and source-cover refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Module.Flat ℤ R] (I : Ideal R)

def reduction (Z : Over (Spec (CommRingCat.of R))) [IsSeparated Z.hom]
    {ν : Type} [Finite ν] (W : ν → Z.left.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hcW : iSup W = ⊤) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Z 1 →ₗ[R]
      ((QuotientTotal.IntegralCechQuotientTotal.bicomplex R Z W I).total (.up ℕ)).homology 1 :=
  (HomologicalComplex.homologyMap (QuotientReduction.IntegralCechQuotientReduction.map R I Z W) 1).hom.comp
    (Naturality.IntegralFirstThreeCechNaturality.equiv R Z W hW hcW).toLinearMap

theorem coordinates (Z : Over (Spec (CommRingCat.of R))) [IsSeparated Z.hom]
    {ν : Type} [Finite ν] (W : ν → Z.left.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hcW : iSup W = ⊤) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Z 1) :
    (QuotientTotal.IntegralCechQuotientTotal.homologyIso R Z W I 1).hom
      (HomologicalComplex.homologyMap (IntegralComparison.Module.IdealQuotient.complexProjection R I
        ((IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R Z W).total (.up ℕ))) 1
          (Naturality.IntegralFirstThreeCechNaturality.equiv R Z W hW hcW x)) = reduction R I Z W hW hcW x := by
  have h := congrArg (fun a => HomologicalComplex.homologyMap a 1)
    (QuotientReduction.IntegralCechQuotientReduction.coordinates R I Z W)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h (Naturality.IntegralFirstThreeCechNaturality.equiv R Z W hW hcW x)

variable {X Y : Over (Spec (CommRingCat.of R))} [IsSeparated X.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) {ι κ : Type} [Finite ι] [Finite κ]
  (U : ι → Y.left.Opens) (V : κ → X.left.Opens) (r : κ → ι)
  (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))
  (hU : ∀ i, IsAffineOpen (U i)) (hcU : iSup U = ⊤)
  (hV : ∀ i, IsAffineOpen (V i)) (hcV : iSup V = ⊤)

theorem naturality (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Y 1) :
    HomologicalComplex.homologyMap (Integral.QuotientCechPullback.IntegralQuotientCechPullback.map R f I U V r hr) 1
      (reduction R I Y U hU hcU x) = reduction R I X V hV hcV (DeRham.Int.pullback f 1 x) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℕ) 1
  have h := congrArg H.map (QuotientReduction.IntegralCechQuotientReduction.naturality R I f U V r hr)
  erw [Functor.map_comp, Functor.map_comp] at h
  exact (ConcreteCategory.congr_hom h (Naturality.IntegralFirstThreeCechNaturality.equiv R Y U hU hcU x)).trans
    (congrArg (H.map (QuotientReduction.IntegralCechQuotientReduction.map R I X V))
      (Naturality.IntegralFirstThreeCechNaturality.naturality R f U V r hr hU hcU hV hcV x))

theorem refinement {Z : Over (Spec (CommRingCat.of R))} [IsSeparated Z.hom]
    {α β : Type} [Finite α] [Finite β] (A : α → Z.left.Opens) (B : β → Z.left.Opens)
    (s : FormalCoproduct.mk β B ⟶ FormalCoproduct.mk α A)
    (hA : ∀ i, IsAffineOpen (A i)) (hcA : iSup A = ⊤)
    (hB : ∀ i, IsAffineOpen (B i)) (hcB : iSup B = ⊤) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Z 1) :
    HomologicalComplex.homologyMap (Integral.QuotientCechRefinement.IntegralQuotientCechRefinement.map R Z I A B s) 1
      (reduction R I Z A hA hcA x) = reduction R I Z B hB hcB x := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℕ) 1
  have h := congrArg H.map (Integral.QuotientCechRefinement.IntegralQuotientCechRefinement.reduction R Z I A B s)
  erw [Functor.map_comp, Functor.map_comp] at h
  exact (ConcreteCategory.congr_hom h (Naturality.IntegralFirstThreeCechNaturality.equiv R Z A hA hcA x)).trans
    (congrArg (H.map (QuotientReduction.IntegralCechQuotientReduction.map R I Z B))
      (RefinementNaturality.IntegralCechRefinementNaturality.naturality R Z A B s hA hcA hB hcB x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ReducedDeRhamNaturality.IntegralCechReducedDeRhamNaturality
