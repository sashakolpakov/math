import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts

/-! # Integral Base Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralBaseIso.IntrinsicPadicIntegralBaseIso

noncomputable section

/-! The canonical Witt-to-p-adic de Rham identification is natural on
the original integral affine section rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of ℤ_[p])))
local notation "W" => WittVector p (ZMod p)
local notation "AW" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "AZ" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℤ_[p] X

local instance coefficients : Algebra W ℤ_[p] := WittAlgebra.PadicWittAlgebra.coefficientAlgebra p
local instance padic (I : X.left.affineOpensᵒᵖ) : Algebra ℤ_[p] ((AW).obj I) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X I.unop.val
local instance witt (I : X.left.affineOpensᵒᵖ) : Algebra W ((AZ).obj I) :=
  WittAlgebra.PadicWittAlgebra.algebra p ((AZ).obj I)
local instance tower (I : X.left.affineOpensᵒᵖ) : IsScalarTower W ℤ_[p] ((AZ).obj I) :=
  IsScalarTower.of_algebraMap_eq' rfl

def source := AW ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W
def target := AZ ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p] ⋙
  (ModuleCat.restrictScalars (WittVector.equiv p).toRingHom).mapHomologicalComplex (.up ℕ)

def component (I : X.left.affineOpensᵒᵖ) :
    (source p X).obj I ≅ (target p X).obj I :=
  WittAlgebra.PadicWittAlgebra.deRhamIso p (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.unop.val)

theorem naturality {I J : X.left.affineOpensᵒᵖ} (α : I ⟶ J) :
    (source p X).map α ≫ (component p X J).hom =
      (component p X I).hom ≫ (target p X).map α := by
  exact SurjectiveBase.SurjectiveBaseDeRham.naturality W ℤ_[p] ((AZ).obj I) (WittVector.equiv p).surjective
    ((AZ).obj J) (((AZ).map α).hom)

def iso : source p X ≅ target p X :=
  NatIso.ofComponents (component p X) (fun α => naturality p X α)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralBaseIso.IntrinsicPadicIntegralBaseIso
