import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphismAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra

/-! # Contragredient Radial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ContragredientRadial.Local

noncomputable section

/-! The inverse-transpose local substitution convention acts through an
actual involutive automorphism of the original spherical Hecke algebra. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra

variable (q : ℕ) [Fact q.Prime]

theorem contragredientHecke_involutive : Function.Involutive (HeckeAutomorphismAction.Local.contragredientHecke q) :=
  HeckeAutomorphismAction.Local.heckeAutomorphism_involutive (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Contragredient.Local.contragredientEquiv ℚ_[q])
    (Contragredient.Local.contragredient_integral_iff q) (Contragredient.Local.contragredient_involutive ℚ_[q])

def contragredientComplexHecke :
    (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) ≃ₐ[ℂ] (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ) (HeckeAutomorphismAction.Local.contragredientHecke q)

theorem contragredientComplexHecke_tmul (c : ℂ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    contragredientComplexHecke q (c ⊗ₜ[ℚ] T) = c ⊗ₜ[ℚ] HeckeAutomorphismAction.Local.contragredientHecke q T := rfl

theorem contragredientComplexHecke_involutive : Function.Involutive (contragredientComplexHecke q) := by
  intro T
  induction T using TensorProduct.inductionOn with
  | add T U hT hU => simp only [map_add, hT, hU]
  | tmul c T =>
      rw [contragredientComplexHecke_tmul, contragredientComplexHecke_tmul,
        contragredientHecke_involutive q T]

theorem radial_hecke_contragredient (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
        ((Radial.Hecke.matrixSubstitution q).comp (Contragredient.Local.contragredient ℚ_[q])) T b.val =
      (Radial.Action.sphericalRadialAction q (HeckeAutomorphismAction.Local.contragredientHecke q T) b).val :=
  (HeckeAutomorphismAction.Local.weilOperator_automorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Contragredient.Local.contragredientEquiv ℚ_[q])
    (Contragredient.Local.contragredient_integral_iff q) (Radial.Hecke.matrixSubstitution q) (Radial.Hecke.radialFixedEmbedding q b) T).symm

def contragredientRadialComplexAlgebra
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :=
  (Radial.Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors).comp (contragredientComplexHecke q).toAlgHom

theorem contragredientRadialComplexAlgebra_dilation
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    contragredientRadialComplexAlgebra q hElementaryDivisors T (Radial.Cyclicity.dilationEquiv q b) =
      Radial.Cyclicity.dilationEquiv q (contragredientRadialComplexAlgebra q hElementaryDivisors T b) :=
  Radial.Algebra.sphericalRadialComplexAlgebra_dilation q hElementaryDivisors _ b

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ContragredientRadial.Local
