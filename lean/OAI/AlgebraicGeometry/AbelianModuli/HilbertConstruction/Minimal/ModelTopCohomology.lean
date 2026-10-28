import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelKoszulDualComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.TopCohomology

/-! # Model Top Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelTopCohomology

noncomputable section

/-! The concentrated local model has a single copy of the residue field in top degree. The residue module is obtained by comparing actual projective resolutions and computing the explicit Koszul cokernel. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

def minimalModelTopResidueIso
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ) (hg : 0 < g)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (rs : List R) (hlen : rs.length = g) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R) (hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R))
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))
    (e : R ≃ₗ[R] Q.complex.X₁) (hI : Q.firstDifferentialIdeal = maximalIdeal R) :
    C.homology g ≅ ModuleCat.of R (ResidueField R) :=
  ModelKoszulDualComparison.minimalModelKoszulDualHomologyIso C g hfin hfree hbound rs hlen hreg hgen hfield Q e hI g ≪≫
    ScalarKoszul.TopCohomology.scalarKoszulDualTopHomologyIso rs g hlen hg ≪≫
      (Submodule.quotEquivOfEq _ _ hgen).toModuleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelTopCohomology
