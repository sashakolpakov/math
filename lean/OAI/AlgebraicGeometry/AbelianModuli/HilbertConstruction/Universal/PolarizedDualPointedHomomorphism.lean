import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.FiniteTargetPointedHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ReverseFiniteHomomorphism

/-! # Polarized Dual Pointed Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.PolarizedDualPointedHomomorphism

noncomputable section

/-! Pointed maps into any polarized dual on any test of fixed Noetherian
projective abelian families automatically preserve the group law. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsNoetherian S] {g h N : ℕ} {δ : Fin h → ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
variable (T : Over S) (D : Dual.Data.DualAbelianData (B.pullback T.hom)) (p : PolarizationData.Polarization D δ)
variable (l : (B.pullback T.hom).FullLevel N) (hδ : ∀ i, 0 < δ i)

include PA PB p l hδ in
theorem universalPolarizedDual_pointedMap_isMonHom
    (f : (A.pullback T.hom).scheme ⟶ D.abelian.scheme)
    (hf : η[(A.pullback T.hom).scheme] ≫ f = η[D.abelian.scheme]) : IsMonHom f := by
  let C : PolarizationData.PolarizedAbelianWithFullLevel h δ N T.left := ⟨B.pullback T.hom, D, p, l⟩
  obtain ⟨r, hr, hfinite, _, _⟩ := C.exists_finite_reverseHomomorphism hδ
  let : IsMonHom r := hr
  let : IsFinite r.left := hfinite
  exact FiniteTargetPointedHomomorphism.universalFiniteTarget_pointedMap_isMonHom A B PA PB T D.abelian r f hf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.PolarizedDualPointedHomomorphism
