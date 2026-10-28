import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.BaseCongruence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.FinitenessProperty
import Mathlib.SetTheory.Cardinal.Order

/-! # Pushforward Cohomology Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness

noncomputable section

/-! An affine direct image preserves finiteness of genuine coherent cohomology in every degree with the original structural coefficient action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

def affinePushforwardCohomologyIso
    {X Y : Scheme.{u}} [Y.IsSeparated] {R : Type u} [CommRing R]
    (f : X ⟶ Y) [IsAffineHom f] (p : Y ⟶ Spec (.of R))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap (f ≫ p)) n).obj M ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) n).obj ((pushforward f).obj M) := by
  classical
  cases n with
  | zero =>
      exact (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap (f ≫ p)) M).toModuleIso ≪≫
        (Coefficient.GlobalSectionsPushforward.schemeGlobalSectionsPushforwardIso f p M).symm.toModuleIso ≪≫
        (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) ((pushforward f).obj M)).symm.toModuleIso
  | succ n =>
      let : LinearOrder Y.affineOpens := IsWellOrder.linearOrder (WellOrderingRel (α := Y.affineOpens))
      exact CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr (Coefficient.GlobalSectionsPushforward.schemeCoefficientMap_comp f p) M (n + 1) ≪≫
        PushforwardZariskiComparison.affineCover_pushforward_cohomologyIso f (Coefficient.ModulePresheaf.schemeCoefficientMap p) M
          (fun U : Y.affineOpens => U.1) (iSup_affineOpens_eq_top Y) (fun U => U.2) n

theorem coefficientCohomologyFinite_affinePushforward_iff
    {X Y : Scheme.{u}} [Y.IsSeparated] {R : Type u} [CommRing R]
    (f : X ⟶ Y) [IsAffineHom f] (p : Y ⟶ Spec (.of R))
    (M : X.Modules) [M.IsQuasicoherent] :
    CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap p) ((pushforward f).obj M) ↔
      CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap (f ≫ p)) M := by
  constructor
  · intro h n
    have := h n
    exact Module.Finite.equiv (affinePushforwardCohomologyIso f p M n).symm.toLinearEquiv
  · intro h n
    have := h n
    exact Module.Finite.equiv (affinePushforwardCohomologyIso f p M n).toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness
