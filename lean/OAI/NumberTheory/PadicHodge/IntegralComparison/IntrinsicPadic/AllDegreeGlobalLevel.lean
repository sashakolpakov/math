import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.LevelNaturality

/-! # All Degree Global Level -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.AllDegreeGlobalLevel.Intrinsic

noncomputable section

/-! The unchanged finite p-adic comparison identifies the original
bounded crystalline cohomology tower in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

abbrev iso (q i : ℕ) := CechQuasiIso.IntrinsicIntegral.homologyIso p X Y f hp q I i

theorem iso_hom (q i : ℕ) : (iso p X Y f hp I q i).hom =
    HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonMap p X Y f hp I q) i ≫
      (GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I q i).hom := rfl

omit [IsSeparated Y.hom] in
theorem target_natural (i : ℕ) :
    HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel.targetMap p X Y f n m hnm I) i ≫
      (GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I n i).hom =
    (GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I m i).hom ≫
      ModuleCat.ofHom (Bounded.CohomologyTransition.map w n m hnm i) := by
  let H := fun (a : GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel.target p X Y f I m ⟶
      GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel.target p X Y f I n) => HomologicalComplex.homologyMap a i
  exact (congrArg (fun a => a ≫ (GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I n i).hom)
    (congrArg H (GeometricComparison.IntrinsicPadic.InjectiveCechMapCoordinates.IntrinsicPadicInjectiveCechMapCoordinates.total p X Y f n m hnm I))).trans
      (GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homology p X Y f n m hnm I i)

theorem natural (i : ℕ) :
    HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel.sourceMap p X n m hnm) i ≫
      (iso p X Y f hp I n i).hom =
    (iso p X Y f hp I m i).hom ≫ ModuleCat.ofHom (Bounded.CohomologyTransition.map w n m hnm i) := by
  rw [iso_hom, iso_hom]
  exact GeometricComparison.ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    (LevelNaturality.IntrinsicIntegral.homology p X Y f hp n m hnm I i).symm
    (target_natural p X Y f n m hnm I i)

theorem iso_one (q : ℕ) : iso p X Y f hp I q 1 =
    GeometricComparison.IntrinsicPadic.IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I q := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.AllDegreeGlobalLevel.Intrinsic
