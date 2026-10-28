import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor

/-! # Zariski Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZariskiLinearity

noncomputable section

/-! The affine-cover Čech comparison preserves the canonical action of every chosen coefficient ring on genuine Zariski cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

def coefficientCechZariskiModuleIso {X : Scheme.{u}} [X.IsSeparated]
    {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).homology (n + 1) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj M := by
  refine ModuleCat.isoMk (ZariskiComparison.coefficientCechZariskiAddIso c M U hU haffine n) ?_
  intro r
  apply ConcreteCategory.hom_ext
  intro x
  have h := ZariskiComparison.coefficientCechZariskiAddIso_naturality c (Global.ModuleScalars.globalModuleScalar M (c r))
    U hU haffine n
  have hm := HomologyScalars.coefficientCech_globalScalar_homologyMap c M U r (n + 1)
  have hv := ConcreteCategory.congr_hom h x
  have hx := ConcreteCategory.congr_hom hm x
  exact ((congrArg (ZariskiComparison.coefficientCechZariskiAddIso c M U hU haffine n).hom hx).symm.trans hv).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZariskiLinearity
