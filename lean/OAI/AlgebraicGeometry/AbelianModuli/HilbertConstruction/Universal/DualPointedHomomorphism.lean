import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.PolarizedDualPointedHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatTensorEpi
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomEpiDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.RepresentingIsoPoints

/-! # Dual Pointed Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.DualPointedHomomorphism

noncomputable section

/-! Pointed maps between supplied polarized duals on arbitrary tests
preserve the group law. The source polarization gives a finite flat cover
by a test of the original Noetherian family. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsNoetherian S] {g h N : ℕ}
variable {δ : Fin g → ℕ} {ε : Fin h → ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
variable (T : Over S) (D : Dual.Data.DualAbelianData (A.pullback T.hom)) (E : Dual.Data.DualAbelianData (B.pullback T.hom))
variable (p : PolarizationData.Polarization D δ) (q : PolarizationData.Polarization E ε)
variable (l : (B.pullback T.hom).FullLevel N) (hε : ∀ i, 0 < ε i)

include PA PB p q l hε in
theorem universalDual_pointedMap_isMonHom
    (f : D.abelian.scheme ⟶ E.abelian.scheme)
    (hf : η[D.abelian.scheme] ≫ f = η[E.abelian.scheme]) : IsMonHom f := by
  let m := p.isogeny.hom ≫ f
  have hm : η[(A.pullback T.hom).scheme] ≫ m = η[E.abelian.scheme] := by
    change η[(A.pullback T.hom).scheme] ≫ (p.isogeny.hom ≫ f) = _
    rw [← Category.assoc, IsMonHom.one_hom, hf]
  let : IsMonHom m := PolarizedDualPointedHomomorphism.universalPolarizedDual_pointedMap_isMonHom A B PA PB T E q l hε m hm
  let : Epi (p.isogeny.hom ⊗ₘ p.isogeny.hom) :=
    FaithfullyFlatTensorEpi.over_tensor_epi_of_flat_surjective p.isogeny.hom p.isogeny.hom
  exact MonoidHomEpiDescent.isMonHom_of_tensor_epi p.isogeny.hom m f rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.DualPointedHomomorphism
