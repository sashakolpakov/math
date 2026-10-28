import OAI.RepresentationTheory.Theta.Adelic.PrincipalRegularIntegral
import OAI.RepresentationTheory.Theta.Adelic.RegularCongruenceReflection
import OAI.RepresentationTheory.Theta.Adelic.IntegralModelCongruence

/-! # Principal Arithmetic Index -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalArithmeticIndex

noncomputable section

/-! Literal coefficient principal groups are commensurable with the
standard integral arithmetic group in the faithful representation. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
open OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel OAI.RepresentationTheory.Theta.Adelic.UnitaryPolynomialEquations
open OAI.RepresentationTheory.Theta.Adelic.PrincipalRegularIntegral OAI.RepresentationTheory.Theta.Adelic.IntegralModelCongruence OAI.RepresentationTheory.Theta.Adelic.RegularCongruenceReflection

variable (F : Type) [Field F] [NumberField F] (d : F)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (N : ℕ) (q : 𝓞 F) (hq : (q : F) = (N : F) * d)

def principalModelGroup : Subgroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).RationalPoints :=
  (PrincipalSubgroup.principalSubgroup F d H N q hq).map (UnitaryAlgebraicModel.regularUnitaryEquiv d H.val).toMonoidHom

theorem principalModel_le_integral :
    principalModelGroup F d H N q hq ≤ IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val) := by
  rintro _ ⟨g, hg, rfl⟩
  exact PrincipalRegularIntegral.principal_regular_stabilizes F d N q hq H g ((PrincipalSubgroup.principalSubgroup_mem_iff F d H N q hq g).mp hg)

theorem reduction_kernel_le_principal :
    (IntegralModelCongruence.integralReduction (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val) N).ker ≤
      (principalModelGroup F d H N q hq).subgroupOf (IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val)) := by
  intro g hg
  let e := UnitaryAlgebraicModel.regularUnitaryEquiv d H.val
  let u := e.symm g.val
  have hu : BallGeometryData.PrincipalLevel N u := by
    apply RegularCongruenceReflection.principal_of_regular_congruence F H N u
    intro i j
    have he : UnitaryPolynomialEquations.regularSU d H.val u = g.val.val := congrArg Subtype.val (e.apply_symm_apply g.val)
    rw [he]
    exact IntegralModelCongruence.integralReduction_coefficients (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val) N g hg i j
  exact ⟨u, (PrincipalSubgroup.principalSubgroup_mem_iff F d H N q hq u).mpr hu, e.apply_symm_apply g.val⟩

theorem principalModel_commensurable (hN : 0 < N) :
    (principalModelGroup F d H N q hq).Commensurable (IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val)) := by
  let : (IntegralModelCongruence.integralReduction (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val) N).ker.FiniteIndex :=
    IntegralModelCongruence.integralReduction_finiteIndex (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val) N hN
  have hi := Subgroup.finiteIndex_of_le (reduction_kernel_le_principal F d H N q hq)
  refine ⟨⟨hi.index_ne_zero⟩, ⟨?_⟩⟩
  rw [Subgroup.relIndex_eq_one.mpr (principalModel_le_integral F d H N q hq)]
  decide

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalArithmeticIndex
