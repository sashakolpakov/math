import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Contraction

/-! # Ordered Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrderedProduct

noncomputable section

/-! Ordered exterior products with the exact concatenation convention
used by ambient equations followed by point parameters. -/
open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction
universe u
variable (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]

def rightWord (p q : ℕ) (v : Fin q → V) : (⋀[R]^p V) →ₗ[R] (⋀[R]^(p + q) V) :=
  ((LinearMap.mulRight R (ExteriorAlgebra.ιMulti R q v)).comp (⋀[R]^p V).subtype).codRestrict
    (⋀[R]^(p + q) V) (fun x => by
      change x.val * ExteriorAlgebra.ιMulti R q v ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ (p + q)
      rw [pow_add]
      exact Submodule.mul_mem_mul x.property (exteriorPower.ιMulti R q v).property)

theorem rightWord_coe (p q : ℕ) (v : Fin q → V) (x : ⋀[R]^p V) :
    (rightWord R V p q v x).val = x.val * ExteriorAlgebra.ιMulti R q v := rfl

theorem rightWord_multi (p q : ℕ) (u : Fin p → V) (v : Fin q → V) :
    rightWord R V p q v (exteriorPower.ιMulti R p u) =
      exteriorPower.ιMulti R (p + q) (Fin.append u v) := by
  apply Subtype.ext
  exact ExteriorAlgebra.ιMulti_mul_ιMulti u v

theorem contraction_rightWord (l : Module.Dual R V) (p q : ℕ)
    (x : ⋀[R]^p V) (v : Fin q → V) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (rightWord R V p q v x).val =
      AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x.val * ExteriorAlgebra.ιMulti R q v +
        (-1 : R) ^ p • (x.val * AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (ExteriorAlgebra.ιMulti R q v)) :=
  KoszulPartial.Contraction.homogeneous_mul R V l p x _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrderedProduct
