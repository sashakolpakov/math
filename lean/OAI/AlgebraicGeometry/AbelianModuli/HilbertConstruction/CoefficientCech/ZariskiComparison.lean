import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechNaturality

/-! # Zariski Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZariskiComparison

noncomputable section

/-! The native coefficient Čech complex computes genuine additive Zariski cohomology naturally. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} [X.IsSeparated] {R : Type u} [CommRing R]

def coefficientCechZariskiAddIso (c : R →+* Γ(X, ⊤)) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (Module.ProductForget.moduleForget R).obj ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).homology (n + 1)) ≅
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (n + 1)).obj M :=
  HomologyForget.coefficientCechComplexHomologyForgetIso c M U (n + 1) ≪≫
    Quasicoherent.CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso M U hU haffine n

theorem coefficientCechZariskiAddIso_naturality (c : R →+* Γ(X, ⊤))
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (Module.ProductForget.moduleForget R).map (HomologicalComplex.homologyMap
        ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map f) (n + 1)) ≫
      (coefficientCechZariskiAddIso c N U hU haffine n).hom =
    (coefficientCechZariskiAddIso c M U hU haffine n).hom ≫
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (n + 1)).map f := by
  apply ConcreteCategory.hom_ext
  intro x
  have h₁ := ConcreteCategory.congr_hom
    (HomologyNaturality.coefficientCechComplexHomologyForgetIso_naturality c f U (n + 1)) x
  have h₂ := ConcreteCategory.congr_hom
    (Quasicoherent.CechNaturality.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso_naturality f U hU haffine n)
      ((HomologyForget.coefficientCechComplexHomologyForgetIso c M U (n + 1)).hom x)
  exact (congrArg
    (Quasicoherent.CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso N U hU haffine n).hom h₁).trans h₂

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZariskiComparison
