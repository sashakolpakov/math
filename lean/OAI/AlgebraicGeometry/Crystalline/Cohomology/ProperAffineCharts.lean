import OAI.NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineBound
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Integral

/-! # Proper Affine Charts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperAffineCharts.CrystallineProperAffineCharts

noncomputable section

/-!
# Proper geometry supplies the finite charts for the native affine computation

The actual finite affine cover of a proper scheme supplies finite-type
coordinate algebras, open-site restriction maps, and the proved integral
and rational crystalline computations on every chart.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]

abbrev Index := (NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover.cover X.hom).I₀

abbrev coordinateRing (i : Index k X) := NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover.coordinateRing X.hom i

def chart (i : Index k X) : Over (Spec (CommRingCat.of k)) :=
  AffineFrameCover.CrystallineAffineFrameCover.affineScheme k (coordinateRing k X i)

def inclusion (i : Index k X) : chart k X i ⟶ X :=
  Over.homMk (NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover.chartMap X.hom i)
    (NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover.chartMap_over X.hom i)

instance inclusion_open (i : Index k X) : IsOpenImmersion (inclusion k X i).left :=
  NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover.chartMap_open X.hom i

theorem covering : (⨆ i : Index k X, (inclusion k X i).left.opensRange) = ⊤ :=
  NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover.chartMaps_cover X.hom

def integralComparison (i : Index k X) (n : ℕ) :
    (Finite.Affine.FiniteAffineCrystalline.complex p k (coordinateRing k X i)).homology n ≅
      ModuleCat.of (Site.CoefficientRing p k) (Site.integralCohomology p k (chart k X i) n) :=
  Finite.Affine.FiniteAffineCrystalline.homologyIso p k (coordinateRing k X i) n

def integralRestriction (i : Index k X) (n : ℕ) :
    Site.integralCohomology p k X n →ₗ[Site.CoefficientRing p k]
      Site.integralCohomology p k (chart k X i) n :=
  CrystallineOpen.Integral.CrystallineOpenCohomology.integralPullback p k (inclusion k X i) n

variable [PerfectRing k p]

def rationalComparison (i : Index k X) (n : ℕ) :
    (Affine.RationalComparison.AffineRationalCrystallineComparison.complex p k (coordinateRing k X i)).homology n ≅
      Site.rationalCohomology p k (chart k X i) n :=
  Affine.RationalComparison.AffineRationalCrystallineComparison.homologyIso p k (coordinateRing k X i) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperAffineCharts.CrystallineProperAffineCharts
