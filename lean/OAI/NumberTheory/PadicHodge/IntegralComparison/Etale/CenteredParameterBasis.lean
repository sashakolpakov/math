import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateSectionKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateTransport

/-! # Centered Parameter Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CenteredParameterBasis

noncomputable section

/-! Centering étale coordinates at a section preserves their actual
differential basis, including after transport through a quotient chart. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra.Etale (MvPolynomial σ R) A]
  (ε : A →ₐ[R] R)

omit [Algebra.Etale (MvPolynomial σ R) A] in
theorem differential (i : σ) :
    KaehlerDifferential.D R A (CoordinateSectionKernel.parameter ε i) =
      KaehlerDifferential.D R A (CoordinateFormBasis.coordinate R A σ i) := by
  unfold CoordinateSectionKernel.parameter CoordinateFormBasis.coordinate
  rw [map_sub]
  change KaehlerDifferential.D R A
    (algebraMap (MvPolynomial σ R) A (MvPolynomial.X i) -
      algebraMap (MvPolynomial σ R) A
        (algebraMap R (MvPolynomial σ R) (CoordinateSectionKernel.point ε i))) = _
  rw [← IsScalarTower.algebraMap_apply, map_sub, Derivation.map_algebraMap, sub_zero]

variable {g : ℕ} (e : Fin g ≃ σ)

def basis : Module.Basis (Fin g) A Ω[A⁄R] :=
  (CoordinateFormBasis.kaehlerBasis R A σ).reindex e.symm

theorem basis_apply (i : Fin g) : basis R A σ e i =
    KaehlerDifferential.D R A (CoordinateSectionKernel.parameter ε (e i)) := by
  rw [basis, Module.Basis.reindex_apply, CoordinateFormBasis.kaehlerBasis_apply]
  exact (differential R A σ ε (e i)).symm

variable (B : Type u) [CommRing B] [Algebra R B] (a : A ≃ₐ[R] B)

def transported : Module.Basis (Fin g) B Ω[B⁄R] :=
  (CoordinateTransport.basis R A B σ a).reindex e.symm

theorem transported_apply (i : Fin g) : transported R A σ e B a i =
    KaehlerDifferential.D R B (a (CoordinateSectionKernel.parameter ε (e i))) := by
  rw [transported, Module.Basis.reindex_apply, CoordinateTransport.basis_apply]
  symm
  unfold CoordinateSectionKernel.parameter
  rw [map_sub, map_sub]
  change KaehlerDifferential.D R B
    (a (algebraMap (MvPolynomial σ R) A (MvPolynomial.X (e i))) -
      a (algebraMap (MvPolynomial σ R) A
        (algebraMap R (MvPolynomial σ R) (CoordinateSectionKernel.point ε (e i))))) = _
  rw [← IsScalarTower.algebraMap_apply, a.commutes, map_sub,
    Derivation.map_algebraMap, sub_zero]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CenteredParameterBasis
