import OAI.AlgebraicGeometry.Crystalline.Cohomology.Foundations
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgePullbackLe
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineCohomologyAdapter

/-! # Good Reduction Operators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators

noncomputable section

/-!
# Native cohomological operators for the good-reduction statement

The actual Frobenius and crystalline pullbacks are transported through
the proved equivalence of the independently constructed small crystalline
sites. De Rham pullback is induced by the generic-fiber scheme map.
These definitions use no good-reduction comparison or finiteness assertion.
The actual de Rham pullback preserves the native Hodge filtration for
every morphism of models.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} [Fact p.Prime] (B : Foundations.MixedCharacteristicDVR.{u} p)

def crystallineSiteEquiv (X : Over (Spec (CommRingCat.of B.R))) (n : ℕ) :
    NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.rationalCohomology p B.k (B.specialFiber X) n ≃ₗ[B.K₀]
      Foundations.rationalCrystalline B X n :=
  NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv
    (p := p) (k := B.k) (X := B.specialFiber X) n

/-- Scheme-induced p-semilinear crystalline Frobenius, over the unramified coefficient field. -/
def crystallineFrobenius (X : Over (Spec (CommRingCat.of B.R))) [IsProper X.hom] (n : ℕ) :
    Foundations.rationalCrystalline B X n →ₛₗ[B.coefficientFrobenius.toRingHom] Foundations.rationalCrystalline B X n :=
  (crystallineSiteEquiv B X n).toLinearMap.comp
    ((NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.rationalFrobenius p B.k (B.specialFiber X) n).comp
      (crystallineSiteEquiv B X n).symm.toLinearMap)

theorem crystallineFrobenius_intertwines (X : Over (Spec (CommRingCat.of B.R))) [IsProper X.hom]
    (n : ℕ) (a : NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.rationalCohomology p B.k (B.specialFiber X) n) :
    crystallineFrobenius B X n (crystallineSiteEquiv B X n a) = crystallineSiteEquiv B X n
      (NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.rationalFrobenius p B.k (B.specialFiber X) n a) := by
  change crystallineSiteEquiv B X n
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.rationalFrobenius p B.k (B.specialFiber X) n
      ((crystallineSiteEquiv B X n).symm (crystallineSiteEquiv B X n a))) = _
  rw [LinearEquiv.symm_apply_apply]

def specialFiberMap {X Y : Over (Spec (CommRingCat.of B.R))} (f : X ⟶ Y) :
    B.specialFiber X ⟶ B.specialFiber Y :=
  (Over.pullback (Spec.map (CommRingCat.ofHom B.reduction))).map f

def genericFiberMap {X Y : Over (Spec (CommRingCat.of B.R))} (f : X ⟶ Y) :
    B.genericFiber X ⟶ B.genericFiber Y :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.K)))).map f

def crystallinePullback {X Y : Over (Spec (CommRingCat.of B.R))}
    [IsProper X.hom] [IsProper Y.hom] (f : X ⟶ Y) (n : ℕ) :
    Foundations.rationalCrystalline B Y n →ₗ[B.K₀] Foundations.rationalCrystalline B X n :=
  (crystallineSiteEquiv B X n).toLinearMap.comp
    ((NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback.rationalPullback p B.k (specialFiberMap B f) n).comp
      (crystallineSiteEquiv B Y n).symm.toLinearMap)

def deRhamPullback {X Y : Over (Spec (CommRingCat.of B.R))} (f : X ⟶ Y) (n : ℕ) :
    Foundations.algebraicDeRham B Y n →ₗ[B.K] Foundations.algebraicDeRham B X n :=
  DeRhamPullbackTo.DeRhamPullback.pullback (genericFiberMap B f) n

theorem deRhamPullback_hodgeFiltration {X Y : Over (Spec (CommRingCat.of B.R))}
    (f : X ⟶ Y) (n : ℕ) (j : ℤ) :
    (Foundations.hodgeFiltration B Y n j).map (deRhamPullback B f n) ≤ Foundations.hodgeFiltration B X n j :=
  HodgePullbackLe.HodgePullback.filtration_map_le (genericFiberMap B f) n j

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators
