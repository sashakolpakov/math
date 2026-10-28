import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison

/-! # Pushforward All Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardAllCohomology

noncomputable section

/-! Affine direct image preserves genuine coefficient cohomology in every degree, including degree zero. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}} [Y.IsSeparated]
variable {R : Type u} [CommRing R] (f : X ⟶ Y) [IsAffineHom f]
variable (c : R →+* Γ(Y, ⊤)) (M : X.Modules) [M.IsQuasicoherent]
variable {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))

def affineCover_pushforward_allCohomologyIso (n : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.appTop.hom.comp c) n).obj M ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj
        ((Scheme.Modules.pushforward f).obj M) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f M
  exact (OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso (f.appTop.hom.comp c) M (fun i => f ⁻¹ᵁ U i)
      (PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top f U hU) (fun i => (ha i).preimage f) n).symm ≪≫
    HomologicalComplex.homologyMapIso (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c M U) n ≪≫
    OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso c ((Scheme.Modules.pushforward f).obj M) U hU ha n

include c U hU ha in
theorem affineCover_pushforward_allCohomology_vanish (n : ℕ)
    (hM : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M n)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((Scheme.Modules.pushforward f).obj M) n) := by
  let : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (f.appTop.hom.comp c) n).obj M) := hM
  change Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj
    ((Scheme.Modules.pushforward f).obj M))
  apply ModuleCat.subsingleton_of_isZero
  exact (affineCover_pushforward_allCohomologyIso f c M U hU ha n).isZero_iff.mp
    (ModuleCat.isZero_of_subsingleton _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardAllCohomology
