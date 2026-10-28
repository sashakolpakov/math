import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralBaseIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientEq

/-! # Integral Reduced Base Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso

noncomputable section

/-! The original integral p-adic de Rham quotient diagram agrees naturally
with its Witt-coefficient presentation at every prime-power level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of ℤ_[p]))) (n : ℕ)
local notation "W" => WittVector p (ZMod p)
local notation "IW" => (Ideal.span {(p : WittVector p (ZMod p))}) ^ (n + 1)
local notation "IZ" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))
local notation "AZ" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℤ_[p] X
local instance coefficients : Algebra W ℤ_[p] := WittAlgebra.PadicWittAlgebra.coefficientAlgebra p

theorem ideal_map : (IW).map (algebraMap W ℤ_[p]) = IZ := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

def coefficientIso : G ⋙ IntegralComparison.Module.IdealQuotient.functor W IW ≅
    IntegralComparison.Module.IdealQuotient.functor ℤ_[p] IZ ⋙ G :=
  ideal_map p n ▸ IdealQuotientEq.IdealQuotientRestriction.iso W ℤ_[p] IW

def source := IntegralBaseIso.IntrinsicPadicIntegralBaseIso.source p X ⋙
  (IntegralComparison.Module.IdealQuotient.functor W IW).mapHomologicalComplex (.up ℕ)

def target := AZ ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p] ⋙
  (IntegralComparison.Module.IdealQuotient.functor ℤ_[p] IZ).mapHomologicalComplex (.up ℕ) ⋙
    (G).mapHomologicalComplex (.up ℕ)

def iso : source p X n ≅ target p X n :=
  Functor.isoWhiskerRight (IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X)
    ((IntegralComparison.Module.IdealQuotient.functor W IW).mapHomologicalComplex (.up ℕ)) ≪≫
      Functor.isoWhiskerLeft (AZ ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p])
        (NatIso.mapHomologicalComplex (coefficientIso p n) (.up ℕ))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso
