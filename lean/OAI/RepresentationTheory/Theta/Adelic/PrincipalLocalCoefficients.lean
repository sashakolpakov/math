import OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralUnitaryMatrices
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods

/-! # Principal Local Coefficients -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalLocalCoefficients

noncomputable section

/-! Entrywise principal congruences supply integral local coordinates
for the rational matrix and its inverse at every finite place. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup

variable (F : Type) [Field F] [NumberField F] {d : F}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem principal_entries_integral (N : ℕ) (g : SpecialUnitary.SU H.val) (hg : BallGeometryData.PrincipalLevel N g) :
    ∀ i j, IsIntegral ℤ (g.val.val i j).re ∧ IsIntegral ℤ (g.val.val i j).im := by
  intro i j
  obtain ⟨a, b, hab⟩ := hg i j
  apply AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralUnitaryMatrices.CM.quadratic_matrix_entry_integral_of_difference d g.val.val i j
  · rw [hab]
    simpa using ((isIntegral_natCast N).mul a.property : IsIntegral ℤ ((N : F) * (a : F)))
  · rw [hab]
    simpa using ((isIntegral_natCast N).mul b.property : IsIntegral ℤ ((N : F) * (b : F)))

theorem principal_local_integral (N : ℕ) (q : 𝓞 F) (hq : (q : F) = (N : F) * d)
    (g : SpecialUnitary.SU H.val) (hg : BallGeometryData.PrincipalLevel N g) (v : FiniteSchwartz.FinitePlace F) :
    RationalSU.rationalLocalSU F H (.inr v) g ∈ IntegralTopology.localSUIntegral F H.val (.inr v) :=
  AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralUnitaryMatrices.CM.local_rational_su_integral_of_coefficients F H g (principal_entries_integral F H N g hg)
    (principal_entries_integral F H N g⁻¹ (PrincipalSubgroup.principalLevel_inv F d H N q hq g hg)) v

theorem rationalLocalSU_difference (g : SpecialUnitary.SU H.val) (v : FiniteSchwartz.FinitePlace F) (i j : Fin 3) :
    (RationalSU.rationalLocalSU F H (.inr v) g).val.val i j -
        (1 : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))) i j =
      Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inr v)
        (g.val.val i j - (1 : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j) := by
  rw [map_sub, SubringCongruence.map_one_entry]
  rfl

theorem principal_local_tuple (N : ℕ) (g : SpecialUnitary.SU H.val) (hg : BallGeometryData.PrincipalLevel N g)
    (hi : BallGeometryData.PrincipalLevel N g⁻¹) (v : FiniteSchwartz.FinitePlace F) (n : ℤ) (hn : n ∣ (N : ℤ)) :
    ∃ a : Fin 2 × Fin 3 × Fin 3 × Fin 2 → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v),
      (∀ i, a i ∈ v.adicCompletionIntegers F) ∧
      ((RationalSU.rationalLocalSU F H (.inr v) g).val.val - 1,
        ((RationalSU.rationalLocalSU F H (.inr v) g)⁻¹).val.val - 1) =
      AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods.CM.quadraticMatrixPair (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d)
        (fun i => algebraMap ℤ (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) n * a i) := by
  let gs : Fin 2 → SpecialUnitary.SU H.val := fun s => if s = 0 then g else g⁻¹
  have hgs (s : Fin 2) : BallGeometryData.PrincipalLevel N (gs s) := by
    dsimp only [gs]
    split_ifs <;> assumption
  choose ar ai hcoeff using fun s i j => hgs s i j
  obtain ⟨c, hc⟩ := hn
  let b : Fin 2 × Fin 3 × Fin 3 × Fin 2 → 𝓞 F := fun p =>
    if p.2.2.2 = 0 then ar p.1 p.2.1 p.2.2.1 else ai p.1 p.2.1 p.2.2.1
  let a : Fin 2 × Fin 3 × Fin 3 × Fin 2 → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v) := fun p =>
    Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (c * (b p : F))
  have ha (p : Fin 2 × Fin 3 × Fin 3 × Fin 2) : a p ∈ v.adicCompletionIntegers F :=
    AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralLocalCoefficients.CM.integral_scalar_at_every_finite_place F _ ((isIntegral_intCast c).mul (b p).property) v
  have hfactor (x : 𝓞 F) :
      Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) ((N : F) * (x : F)) =
        algebraMap ℤ (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) n * Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (c * (x : F)) := by
    have hNc : (N : F) = (n : F) * (c : F) := by exact_mod_cast hc
    have he : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) ((N : F) * (x : F)) =
        (n : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) * Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (c * (x : F)) := by
      rw [hNc]
      simp only [map_mul, map_intCast, mul_assoc]
    exact he.trans (congrArg (fun z : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v) =>
      z * Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (c * (x : F)))
        (map_intCast (algebraMap ℤ (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))) n).symm)
  have he (s : Fin 2) (i j : Fin 3) :=
    (rationalLocalSU_difference F H (gs s) v i j).trans
      (congrArg (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inr v)) (hcoeff s i j))
  refine ⟨a, ha, ?_⟩
  apply Prod.ext
  · apply Matrix.ext
    intro i j
    have h := he 0 i j
    simp only [gs, ite_eq_left rfl] at h
    apply h.trans
    apply QuadraticAlgebra.ext
    · simpa [Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal, Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods.CM.quadraticMatrixPair, a, b] using hfactor (ar 0 i j)
    · simpa [Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal, Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods.CM.quadraticMatrixPair, a, b] using hfactor (ai 0 i j)
  · apply Matrix.ext
    intro i j
    have h := he 1 i j
    simp only [gs, show (1 : Fin 2) ≠ 0 by decide, ite_false, map_inv] at h
    apply h.trans
    apply QuadraticAlgebra.ext
    · simpa [Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal, Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods.CM.quadraticMatrixPair, a, b] using hfactor (ar 1 i j)
    · simpa [Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal, Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods.CM.quadraticMatrixPair, a, b] using hfactor (ai 1 i j)

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalLocalCoefficients
