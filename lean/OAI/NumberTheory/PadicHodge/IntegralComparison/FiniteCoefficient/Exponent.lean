import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf

/-! # Exponent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Exponent

noncomputable section

/-! The actual pro-étale cohomology with coefficients in Z/ℓⁿ is
annihilated by ℓⁿ in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction

universe u

theorem coefficient_nsmul_id (ℓ n : ℕ) (X : Scheme.{u}) :
    (ℓ ^ n) • (𝟙 (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X)) = 0 := by
  ext U s
  change ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change (ℓ ^ n) • s.down x = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem cohomology_nsmul (ℓ n : ℕ) (X : Scheme.{u}) (d : ℕ)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H d) : (ℓ ^ n) • x = 0 := by
  have hmap (m : ℕ) :
      Sheaf.H.map (m • (𝟙 (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X))) d x = m • x := by
    induction m with
    | zero => simp only [zero_smul, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]
    | succ m ih => rw [succ_nsmul, Sheaf.H.map_add_apply, ih, Sheaf.H.map_id_apply,
        succ_nsmul]
  rw [← hmap, coefficient_nsmul_id, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Exponent
