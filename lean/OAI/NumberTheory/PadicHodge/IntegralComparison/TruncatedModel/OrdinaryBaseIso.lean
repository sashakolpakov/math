import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts

/-! # Ordinary Base Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryBaseIso.Ordinary

noncomputable section

/-! The Witt-relative ordinary frame diagram is naturally the ordinary
de Rham diagram of the same model over its actual truncated base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "AW" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison.rings p k n X Y f hp
local notation "AS" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras S X

local instance truncated (I : X.left.affineOpensᵒᵖ) : Algebra S ((AW).obj I) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X I.unop.val
local instance witt (I : X.left.affineOpensᵒᵖ) : Algebra W ((AS).obj I) :=
  Truncated.SmoothFrame.Complex.wittAlgebra p k n ((AS).obj I)
local instance tower (I : X.left.affineOpensᵒᵖ) : IsScalarTower W S ((AS).obj I) :=
  IsScalarTower.of_algebraMap_eq' rfl

def source := PrincipalComplex.Comparison.ordinaryComplexes p k n X Y f hp
def target := AS ⋙ OrdinaryDeRhamFunctor.Ordinary.functor S ⋙
  (ModuleCat.restrictScalars (algebraMap W S)).mapHomologicalComplex (.up ℕ)

def component (I : X.left.affineOpensᵒᵖ) :
    (source p k n X Y f hp).obj I ≅ (target p k n X).obj I :=
  GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso W S ((AS).obj I) Ideal.Quotient.mk_surjective

theorem naturality {I J : X.left.affineOpensᵒᵖ} (α : I ⟶ J) :
    (source p k n X Y f hp).map α ≫ (component p k n X Y f hp J).hom =
      (component p k n X Y f hp I).hom ≫ (target p k n X).map α := by
  exact GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.naturality W S ((AS).obj I) Ideal.Quotient.mk_surjective
    ((AS).obj J) (((AS).map α).hom)

def iso : source p k n X Y f hp ≅ target p k n X :=
  NatIso.ofComponents (component p k n X Y f hp) (fun α => naturality p k n X Y f hp α)

def pdIso : PrincipalComplex.Comparison.pdComplexes p k n X Y f hp ≅
    target p k n X :=
  PrincipalComplex.Comparison.iso p k n X Y f hp ≪≫ iso p k n X Y f hp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryBaseIso.Ordinary
