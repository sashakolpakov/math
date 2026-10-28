import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IdentityRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IdentityForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Naturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Functor
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinementCoefficient

/-! # Refinement Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.RefinementNaturality.IntegralCechRefinementNaturality

noncomputable section

/-! Actual cover refinement preserves the original integral
de Rham coordinates in the nonnegative Cech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def map := CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map U V r K

omit [Module.Flat ℤ R] [IsSeparated X.hom] [Finite ι] [Finite κ] in
theorem bicomplex_identity : CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R (𝟙 X) U V r.f
    (Cech.IdentityRefinement.CechIdentityRefinement.coverLE X.left U V r) =
      CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap U V r K := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact Cech.IdentityRefinement.CechIdentityRefinement.map R X.left U V r ((K).X q)
    ((IntegralFirst.ThreePullback.IntegralFirstThreePullback.presheafMap (𝟙 X)).f q) (DeRham.IdentityForms.DeRhamIdentityForms.firstThree_component R X q)

omit [Module.Flat ℤ R] [IsSeparated X.hom] [Finite ι] [Finite κ] in
theorem total_identity : HomologicalComplex₂.total.map
    (CoordinatePullback.IntegralCechCoordinatePullback.coordinateMap R (𝟙 X) U V r.f
      (Cech.IdentityRefinement.CechIdentityRefinement.coverLE X.left U V r)) (.up ℕ) = IntegralCechRefinementNaturality.map R X U V r :=
  congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex_identity R X U V r)

variable (hU : ∀ i, IsAffineOpen (U i)) (hcU : iSup U = ⊤)
  (hV : ∀ i, IsAffineOpen (V i)) (hcV : iSup V = ⊤)

theorem naturality (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1) :
    HomologicalComplex.homologyMap (IntegralCechRefinementNaturality.map R X U V r) 1
      (Naturality.IntegralFirstThreeCechNaturality.equiv R X U hU hcU x) =
        Naturality.IntegralFirstThreeCechNaturality.equiv R X V hV hcV x :=
  (congrArg (fun a : (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U).total (.up ℕ) ⟶
    (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X V).total (.up ℕ) => HomologicalComplex.homologyMap a 1
    (Naturality.IntegralFirstThreeCechNaturality.equiv R X U hU hcU x)) (total_identity R X U V r).symm).trans
    ((Naturality.IntegralFirstThreeCechNaturality.naturality R (𝟙 X) U V r.f
      (Cech.IdentityRefinement.CechIdentityRefinement.coverLE X.left U V r) hU hcU hV hcV x).trans
        (congrArg (Naturality.IntegralFirstThreeCechNaturality.equiv R X V hV hcV)
          (LinearMap.congr_fun (DeRham.Functor.pullback_id X 1) x)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.RefinementNaturality.IntegralCechRefinementNaturality
