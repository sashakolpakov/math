import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveBaseProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealQuotientRestrictionProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryReductionProduct

/-! # Reduced Base Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedBaseProduct.Intrinsic

noncomputable section

/-! The literal Witt-to-p-adic finite ordinary comparison preserves
the quotient wedge. Its source, target, and coefficient isomorphism
are exactly those in the accepted native comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of ℤ_[p]))) (n : ℕ)
local notation "W" => WittVector p (ZMod p)
local notation "IW" => (Ideal.span {(p : W)}) ^ (n+1)
local notation "IZ" => (Ideal.span {(p : ℤ_[p])}) ^ (n+1)
local notation "AW" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "AZ" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℤ_[p] X
local instance coefficients : Algebra W ℤ_[p] := GeometricComparison.WittAlgebra.PadicWittAlgebra.coefficientAlgebra p
local instance padic (V : X.left.affineOpensᵒᵖ) : Algebra ℤ_[p] ((AW).obj V) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X V.unop.val
local instance padicTarget (V : X.left.affineOpensᵒᵖ) : Algebra ℤ_[p] ((AZ).obj V) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X V.unop.val
local instance witt (V : X.left.affineOpensᵒᵖ) : Algebra W ((AZ).obj V) :=
  GeometricComparison.WittAlgebra.PadicWittAlgebra.algebra p ((AZ).obj V)
local instance tower (V : X.left.affineOpensᵒᵖ) : IsScalarTower W ℤ_[p] ((AZ).obj V) :=
  IsScalarTower.of_algebraMap_eq' rfl

omit n in
theorem base_wedge (V : X.left.affineOpensᵒᵖ) (i j : ℕ)
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W ((AW).obj V) i)
    (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W ((AW).obj V) j) :
    (((GeometricComparison.IntrinsicPadic.IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app V).f (i+j))
        (IntegralDeRham.DeRhamWedge.wedge W ((AW).obj V) i j x y) =
      IntegralDeRham.DeRhamWedge.wedge ℤ_[p] ((AZ).obj V) i j
        (((GeometricComparison.IntrinsicPadic.IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app V).f i x)
        (((GeometricComparison.IntrinsicPadic.IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app V).f j y) := by
  let aZ : Algebra ℤ_[p] ((AZ).obj V) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X V.unop.val
  let aW : Algebra W ((AZ).obj V) := @GeometricComparison.WittAlgebra.PadicWittAlgebra.algebra p inferInstance
    ((AZ).obj V) inferInstance aZ
  let hT : IsScalarTower W ℤ_[p] ((AZ).obj V) := IsScalarTower.of_algebraMap_eq' rfl
  exact @SurjectiveBaseProduct.hom_wedge W ℤ_[p] ((AZ).obj V)
    inferInstance inferInstance inferInstance (GeometricComparison.WittAlgebra.PadicWittAlgebra.coefficientAlgebra p) aZ aW hT
    (WittVector.equiv p).surjective i j x y

theorem coefficient_mk (M : ModuleCat.{0} ℤ_[p]) (x : M) :
    ((GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.coefficientIso p n).hom.app M)
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  IdealQuotientRestrictionProduct.isoOfEq_mk W ℤ_[p] IW M IZ
    (GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.ideal_map p n) x

theorem map_mk (V : X.left.affineOpensᵒᵖ) (i : ℕ)
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W ((AW).obj V) i) :
    ((GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n).hom.app V).f i
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (show AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℤ_[p] ((AZ).obj V) i from
        (((GeometricComparison.IntrinsicPadic.IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app V).f i x)) :=
  coefficient_mk p n _ _

theorem map_wedge (V : X.left.affineOpensᵒᵖ) (i j : ℕ)
    (x : ((GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.source p X n).obj V).X i)
    (y : ((GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.source p X n).obj V).X j) :
    ((GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n).hom.app V).f (i+j)
        (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.quotientPairing W IW ((AW).obj V) i j x y) =
      OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.quotientPairing ℤ_[p] IZ ((AZ).obj V) i j
        (((GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n).hom.app V).f i x)
        (((GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n).hom.app V).f j y) := by
  obtain ⟨x, rfl⟩ := (IW • ⊤ : Submodule W (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W ((AW).obj V) i)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (IW • ⊤ : Submodule W (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W ((AW).obj V) j)).mkQ_surjective y
  exact (map_mk p X n V (i+j) (IntegralDeRham.DeRhamWedge.wedge W ((AW).obj V) i j x y)).trans
    ((congrArg (IZ • ⊤ : Submodule ℤ_[p] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℤ_[p] ((AZ).obj V) (i+j))).mkQ
      (base_wedge p X V i j x y)).trans
        (congrArg₂ (fun x y => OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.quotientPairing
          ℤ_[p] IZ ((AZ).obj V) i j x y)
          (map_mk p X n V i x).symm (map_mk p X n V j y).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedBaseProduct.Intrinsic
