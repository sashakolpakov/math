import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleLinear
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerFrobeniusIdentification
import OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusFactorization

/-! # Frobenius Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusCohomology.FiniteFieldFrobeniusGeometry

noncomputable section

/-! Completion's original geometric H¹ Frobenius is exactly the original integral-coefficient pullback by IntegralComparison's inverse-field Frobenius automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

private theorem pullback_comp_of_left_id (ℓ : ℕ) [Fact ℓ.Prime]
    {Y : Scheme.{0}} (f g : Y ⟶ Y) (hf : AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ f = LinearMap.id) :
    AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (f ≫ g) = AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ g := by
  rw [← AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality.Construction.algebraicEllAdicH1Pullback_comp, hf, LinearMap.id_comp]

theorem geometricH1Frobenius_eq_field_pullback
    (p : ℕ) [Fact p.Prime] (A : Over (Spec (.of (ZMod p)))) (ℓ : ℕ) [Fact ℓ.Prime] :
    AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.geometricH1Frobenius ℓ (ZMod p) A =
      AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ
        (IntegralComparison.Frobenius.Geometry.geometricFiberIso A.hom (IntegralComparison.Frobenius.Geometry.geometricFrobenius p 1 (ZMod p) (by simp))).hom := by
  have hF : AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (FrobeniusFactorization.FiniteFieldFrobeniusGeometry.absoluteOnGeometricFiber (ZMod p) A) = LinearMap.id := by
    change AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ
      (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius (ZMod p) (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A)
        (FrobeniusFactorization.FiniteFieldFrobeniusGeometry.geometricFiberBaseMap (ZMod p) A)) = LinearMap.id
    rw [PrimePowerFrobeniusIdentification.FiniteFieldFrobeniusGeometry.qPower_eq_absolute]
    exact ProEtaleLinear.ProEtaleFrobeniusCohomology.algebraic_pullback p Fact.out _ _ ℓ
  let Y := AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A
  let f : Y ⟶ Y := FrobeniusFactorization.FiniteFieldFrobeniusGeometry.absoluteOnGeometricFiber (ZMod p) A
  let g : Y ⟶ Y := (IntegralComparison.Frobenius.Geometry.geometricFiberIso A.hom (IntegralComparison.Frobenius.Geometry.geometricFrobenius p 1 (ZMod p) (by simp))).hom
  have h : AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricSchemeFrobenius (ZMod p) A = f ≫ g :=
    FrobeniusFactorization.FiniteFieldFrobeniusGeometry.geometricFrobenius_factorization (ZMod p) A p 1 (by simp)
  exact (congrArg (fun t : Y ⟶ Y => AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ t) h).trans
    (pullback_comp_of_left_id ℓ f g hF)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusCohomology.FiniteFieldFrobeniusGeometry
