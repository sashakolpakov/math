import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairSectionAlgebraPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebra
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralBaseIso

/-! # Base Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.BaseIso.IntrinsicPadicGeometricBaseIso

noncomputable section

/-! The original Witt-to-p-adic de Rham coordinate isomorphism
commutes with actual geometric maps of integral affine sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X Y : Over (Spec (CommRingCat.of ℤ_[p]))} (u : X ⟶ Y)

local notation "W" => WittVector p (ZMod p)
local notation "S" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))

local instance coefficients : Algebra W ℤ_[p] := WittAlgebra.PadicWittAlgebra.coefficientAlgebra p

def wittMap : T ⋙ IntegralBaseIso.IntrinsicPadicIntegralBaseIso.source p Y ⟶ S ⋙ IntegralBaseIso.IntrinsicPadicIntegralBaseIso.source p X :=
  Functor.whiskerRight (IntegralAlgebra.IntrinsicPadicGeometricIntegralAlgebra.transformation p u) (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W)

def padicMap : T ⋙ IntegralBaseIso.IntrinsicPadicIntegralBaseIso.target p Y ⟶ S ⋙ IntegralBaseIso.IntrinsicPadicIntegralBaseIso.target p X :=
  Functor.whiskerRight (Affine.PairSectionAlgebraPullback.AffinePairSectionAlgebraPullback.transformation ℤ_[p] u)
    (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p] ⋙ (G).mapHomologicalComplex (.up ℕ))

theorem component (U : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    (wittMap p u).app U ≫ (IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app ((S).obj U) =
      (IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p Y).hom.app ((T).obj U) ≫ (padicMap p u).app U := by
  let A := Γ(Y.left, U.unop.val.2.val)
  let B := Γ(X.left, U.unop.val.1.val)
  let : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] Y U.unop.val.2.val
  let : Algebra ℤ_[p] B := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U.unop.val.1.val
  let : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A
  let : Algebra W B := WittAlgebra.PadicWittAlgebra.algebra p B
  let : IsScalarTower W ℤ_[p] A := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower W ℤ_[p] B := IsScalarTower.of_algebraMap_eq' rfl
  exact SurjectiveBase.SurjectiveBaseDeRham.naturality W ℤ_[p] A (WittVector.equiv p).surjective B
    (OpenSectionPullback.DeRham.sectionPullbackLE u U.unop.val.2.val U.unop.val.1.val U.unop.property)

theorem naturality : wittMap p u ≫ Functor.whiskerLeft S (IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom =
    Functor.whiskerLeft T (IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p Y).hom ≫ padicMap p u := by
  apply NatTrans.ext
  funext U
  exact component p u U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.BaseIso.IntrinsicPadicGeometricBaseIso
