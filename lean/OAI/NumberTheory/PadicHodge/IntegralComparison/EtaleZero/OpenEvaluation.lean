import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ResolutionSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartEvaluationCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.OpenSections

/-! # Open Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.OpenEvaluation

noncomputable section

/-! The original affine open comparison in the evaluated global-resolution coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  (g : (Crystalline.Presentation.affineScheme k C).left ⟶ Y) [IsOpenImmersion g]
  (hg : g ≫ fY = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) fY 0))
  (U : Y.Opens) (eU : g.opensRange = U)

theorem factorization : OpenSections.map p k C σ g hg I ≫
    (Bounded.ChartEvaluationCoordinates.iso fY g 0 U eU I).hom =
      ResolutionSections.map p k C σ (Bounded.GeometricResolution.resolution g hg 0 I) ≫
        (Bounded.GeometricOpenSections.complexIso g hg 0 I).inv ≫
          (Bounded.ChartEvaluationCoordinates.iso fY g 0 U eU I).hom :=
  (Category.assoc _ _ _).trans
    (congrArg (fun a => a ≫ (Bounded.GeometricOpenSections.complexIso g hg 0 I).inv ≫
      (Bounded.ChartEvaluationCoordinates.iso fY g 0 U eU I).hom)
        (ResolutionSections.restricted p k C σ g hg I).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.OpenEvaluation
