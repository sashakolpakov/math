import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.FiniteTargetFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ReverseFiniteHomomorphism

/-! # Polarized Dual Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.PolarizedDualFieldDetection

noncomputable section

/-! Every field pullback detects pointed maps into a supplied polarized
dual on any test scheme of fixed Noetherian projective abelian families. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} [IsNoetherian S] {g h N : ℕ} {δ : Fin h → ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
variable (T : Over S) (D : Dual.Data.DualAbelianData (B.pullback T.hom)) (p : PolarizationData.Polarization D δ)
variable (l : (B.pullback T.hom).FullLevel N) (hδ : ∀ i, 0 < δ i)

include PA PB p l hδ in
theorem universalPolarizedDual_pointedMap_eq_of_fieldPullbacks
    (f q : (A.pullback T.hom).scheme ⟶ D.abelian.scheme)
    (hf : η[(A.pullback T.hom).scheme] ≫ f = η[D.abelian.scheme])
    (hq : η[(A.pullback T.hom).scheme] ≫ q = η[D.abelian.scheme])
    (he : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let C : PolarizationData.PolarizedAbelianWithFullLevel h δ N T.left := ⟨B.pullback T.hom, D, p, l⟩
  obtain ⟨r, hr, hfinite, _, _⟩ := C.exists_finite_reverseHomomorphism hδ
  let : IsMonHom r := hr
  let : IsFinite r.left := hfinite
  exact FiniteTargetFieldDetection.universalFiniteTarget_pointedMap_eq_of_fieldPullbacks A B PA PB T D.abelian.scheme r f q hf hq he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.PolarizedDualFieldDetection
