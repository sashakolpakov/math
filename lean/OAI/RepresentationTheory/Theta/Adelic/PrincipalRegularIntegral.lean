import OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices

/-! # Principal Regular Integral -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalRegularIntegral

noncomputable section

/-! Deep coefficient principal groups preserve the actual standard
integral lattice in the six-dimensional faithful representation. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
open OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder OAI.RepresentationTheory.Theta.Adelic.SubringCongruence OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel
open OAI.RepresentationTheory.Theta.Adelic.UnitaryPolynomialEquations

variable (F : Type) [Field F] [NumberField F] (d : F)
variable (N : ℕ) (q : 𝓞 F) (hq : (q : F) = (N : F) * d)

omit [NumberField F] in
theorem order_regular_integral (x : PrincipalCoefficientOrder.coefficientOrder F d N q hq) (i j : Fin 2) :
    IsIntegral ℤ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticRegular d x.val i j) := by
  obtain ⟨a, b, h⟩ := x.property
  rw [h]
  fin_cases i <;> fin_cases j
  · exact a.property
  · change IsIntegral ℤ (d * ((N : F) * (b : F)))
    have he : d * ((N : F) * (b : F)) = (q : F) * (b : F) := by rw [hq]; ring
    exact he.symm ▸ q.property.mul b.property
  · exact (isIntegral_natCast N).mul b.property
  · exact a.property

variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

omit [NumberField F] in
include q hq in
theorem principal_regular_integral (g : SpecialUnitary.SU H.val) (hg : BallGeometryData.PrincipalLevel N g) :
    ∀ i j, IsIntegral ℤ ((UnitaryPolynomialEquations.regularSU d H.val g).val i j) := by
  have hmem := (PrincipalSubgroup.principalSubgroup_mem_iff F d H N q hq g).mpr hg
  change PrincipalSubgroup.suSpecialLinear H.val g ∈
    SubringCongruence.congruenceImage (PrincipalCoefficientOrder.coefficientOrder F d N q hq) (PrincipalCoefficientOrder.coefficientIdeal F d N q hq) at hmem
  obtain ⟨u, _, hu⟩ := hmem
  have he (i j : Fin 3) : g.val.val i j ∈ PrincipalCoefficientOrder.coefficientOrder F d N q hq := by
    have hh := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) => A.val i j) hu
    change (u.val i j : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) = g.val.val i j at hh
    exact hh ▸ (u.val i j).property
  intro i j
  obtain ⟨⟨i, a⟩, rfl⟩ := Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex.surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex.surjective j
  change IsIntegral ℤ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d g.val.val _ _)
  rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_entry]
  exact order_regular_integral F d N q hq ⟨g.val.val i j, he i j⟩ a b

include q hq in
theorem principal_regular_stabilizes (g : SpecialUnitary.SU H.val) (hg : BallGeometryData.PrincipalLevel N g) :
    UnitaryAlgebraicModel.regularUnitaryEquiv d H.val g ∈
      (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).latticeStabilizer (NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F 6) := by
  apply (NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction.standard_lattice_stabilizer_iff_integral _ _).mpr
  let M : Matrix (Fin 6) (Fin 6) (𝓞 F) :=
    fun i j => ⟨(UnitaryPolynomialEquations.regularSU d H.val g).val i j, principal_regular_integral F d N q hq H g hg i j⟩
  have hdet : M.det = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [RingHom.map_det, map_one]
    exact (UnitaryPolynomialEquations.regularSU d H.val g).property
  exact ⟨⟨M, hdet⟩, rfl⟩

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalRegularIntegral
