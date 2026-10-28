import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.ParameterKoszulResolution
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ResolutionHomologyComparison

/-! # Model Koszul Dual Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelKoszulDualComparison

noncomputable section

/-! A finite free cochain model with the established local support and minimal coefficient properties has the same cohomology as the dual of the explicit regular-parameter Koszul resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

def minimalModelKoszulDualHomologyIso
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (rs : List R) (hlen : rs.length = g) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R) (hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R))
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))
    (e : R ≃ₗ[R] Q.complex.X₁) (hI : Q.firstDifferentialIdeal = maximalIdeal R) (n : ℕ) :
    C.homology n ≅ (HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) (Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs)).homology n :=
  HomologicalComplex.homologyMapIso (HilbertConstruction.Finite.FreeDoubleDualComplex.finiteFreeDoubleDualComplexIso C hfin hfree) n ≪≫
    Dual.ResolutionHomologyComparison.dualProjectiveResolutionHomologyIso
      (AugmentedDualProjectiveResolution.minimalDualProjectiveResolution C g hfin hfree hbound rs hlen hreg hgen hfield Q e hI)
      (Regular.ParameterKoszulResolution.regularParameterKoszulResolution rs hreg hgen) n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelKoszulDualComparison
