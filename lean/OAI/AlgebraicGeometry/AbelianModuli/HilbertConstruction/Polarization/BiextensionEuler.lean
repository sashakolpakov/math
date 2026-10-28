import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PolarizationCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback

/-! # Biextension Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical polarization biextension on the actual square of the
abelian scheme has its degree-normalized cohomology and Euler characteristic. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped BigOperators
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.polarizationBiextension_cohomology
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    let p := pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom;
    let L := A.dual.poincareAt A.polarization.isogeny.hom;
    (∀ q : ℕ, q ≠ g → IsZero
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj L.sheaf)) ∧
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) g).obj L.sheaf) =
      (∏ i, δ i) ^ 2 :=
  A.poincarePolarization_cohomology hg hN hNk
    (Picard.TestFamilyPullback.familySchemeFunctor_map_isPullback A.abelian.scheme A.polarization.isogeny.hom)

theorem PolarizationData.PolarizedAbelianWithFullLevel.polarizationBiextension_euler
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic
      (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom)
      (A.dual.poincareAt A.polarization.isogeny.hom).sheaf =
        (-1 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ) ^ 2 :=
  A.poincarePolarization_euler hg hN hNk
    (Picard.TestFamilyPullback.familySchemeFunctor_map_isPullback A.abelian.scheme A.polarization.isogeny.hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
