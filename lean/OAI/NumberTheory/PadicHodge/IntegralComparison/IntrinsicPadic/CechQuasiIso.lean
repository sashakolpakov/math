import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalLevel
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso

/-! # Cech Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechQuasiIso.IntrinsicIntegral

noncomputable section

/-! The existing native p-adic quotient comparison is a genuine
quasi-isomorphism in all degrees. Its map is unchanged; the affine
intersection quasi-isomorphisms already hold in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)
  (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

theorem quasiIso : QuasiIso (GeometricComparison.IntrinsicPadic.IntegralCechOne.IntrinsicPadicIntegralCechHOne.map p X Y f hp n J) :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.quasiIso.{1,2} R E
    (GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n J)
    (GeometricComparison.IntrinsicPadic.IntegralCechOne.IntrinsicPadicIntegralCechHOne.intersection_quasiIso p X Y f hp n J)

variable (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

omit J in
theorem level_quasiIso : QuasiIso (GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonMap p X Y f hp I n) :=
  quasiIso p X Y f hp n (BoundedCrystalline.CrystallineCohomology.resolution
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n I)

omit J in
def homologyIso (i : ℕ) : (GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel.source p X n).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
      (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n i) := by
  letI := level_quasiIso p X Y f hp n I
  exact isoOfQuasiIsoAt (GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonMap p X Y f hp I n) i ≪≫
    GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I n i

omit J in
theorem homologyIso_one : homologyIso p X Y f hp n I 1 =
    GeometricComparison.IntrinsicPadic.IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I n := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechQuasiIso.IntrinsicIntegral
