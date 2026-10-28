import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Action
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SphericalMultiplication
import OAI.RepresentationTheory.Theta.Geometric.Active.Algebra
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Algebra -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra

noncomputable section

/-! The concrete radial coset sum is an algebra action. Commutativity
comes from the full ElementaryDivisors input on the actual active special-linear sector. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

theorem sl3_hecke_commutative (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (T U : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) : T * U = U * T := by
  let e := RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q (0 : Fin 1)
  apply e.injective
  have hm : e T * e U = e U * e T := Subtype.ext
    (AbelianScheme.TateComparison.Commutativity.spherical_mul_comm 1 q hElementaryDivisors (e T).val (e U).val)
  exact (e.map_mul T U).trans (hm.trans (e.map_mul U T).symm)

theorem complex_hecke_commutative (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (T U : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) : T * U = U * T := by
  let : CommRing (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :=
    { (inferInstance : Ring (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q)) with mul_comm := sl3_hecke_commutative q hElementaryDivisors }
  exact mul_comm T U

theorem sphericalRadialAction_mul_reverse (T U : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    Action.sphericalRadialAction q (T * U) b =
      Action.sphericalRadialAction q U (Action.sphericalRadialAction q T b) := by
  apply Subtype.ext
  exact congrArg (fun x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q) => x.val)
    (SphericalMultiplication.Radial.weilAction_mul_reverse (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (Hecke.matrixSubstitution q) T U (Hecke.radialFixedEmbedding q b))

theorem sphericalRadialAction_one (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) : Action.sphericalRadialAction q 1 b = b := by
  apply Subtype.ext
  exact congrArg (fun x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q) => x.val)
    (SphericalMultiplication.Radial.weilAction_one (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (Hecke.matrixSubstitution q) (Hecke.radialFixedEmbedding q b))

def sphericalRadialLinear : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₗ[ℚ] Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) where
  toFun := Action.sphericalRadialAction q
  map_add' T U := by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q) => x.val)
      (LinearMap.congr_fun
      ((SphericalMultiplication.Radial.weilActionLinear (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q)).map_add T U)
      (Hecke.radialFixedEmbedding q b))
  map_smul' r T := by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q) => x.val)
      (LinearMap.congr_fun
      ((SphericalMultiplication.Radial.weilActionLinear (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q)).map_smul r T)
      (Hecke.radialFixedEmbedding q b))

def sphericalRadialAlgebra (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) where
  __ := sphericalRadialLinear q
  map_zero' := (sphericalRadialLinear q).map_zero
  map_one' := by
    apply LinearMap.ext
    intro b
    exact sphericalRadialAction_one q b
  map_mul' T U := by
    apply LinearMap.ext
    intro b
    change Action.sphericalRadialAction q (T * U) b =
      Action.sphericalRadialAction q T (Action.sphericalRadialAction q U b)
    rw [sl3_hecke_commutative q hElementaryDivisors T U]
    exact sphericalRadialAction_mul_reverse q U T b
  commutes' r := by
    change sphericalRadialLinear q ((algebraMap ℚ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q)) r) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    have h1 : sphericalRadialLinear q 1 = 1 := by
      apply LinearMap.ext
      intro b
      exact sphericalRadialAction_one q b
    rw [h1, Algebra.algebraMap_eq_smul_one]

def sphericalRadialComplexAlgebra (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :=
  AlgHom.liftEquiv ℚ ℂ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q))
    (sphericalRadialAlgebra q hElementaryDivisors)

theorem sphericalRadialComplexAlgebra_tmul
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (c : ℂ)
    (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    sphericalRadialComplexAlgebra q hElementaryDivisors (c ⊗ₜ[ℚ] T) b = c • Action.sphericalRadialAction q T b := rfl

theorem sphericalRadialComplexAlgebra_dilation
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    sphericalRadialComplexAlgebra q hElementaryDivisors T (Cyclicity.dilationEquiv q b) =
      Cyclicity.dilationEquiv q (sphericalRadialComplexAlgebra q hElementaryDivisors T b) := by
  induction T using TensorProduct.inductionOn with
  | tmul c T =>
      rw [sphericalRadialComplexAlgebra_tmul, sphericalRadialComplexAlgebra_tmul,
        Action.sphericalRadialAction_dilation, map_smul]
  | add T U hT hU =>
      simp only [map_add, LinearMap.add_apply, hT, hU]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra
