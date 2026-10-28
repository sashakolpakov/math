import OAI.RepresentationTheory.Theta.Adelic.PrincipalArithmeticIndex
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicAlgebraicPlaces
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.CompactPlaceArithmetic
import OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete

/-! # Principal Archimedean Quotient -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalArchimedeanQuotient

noncomputable section

/-! The actual principal subgroup is discrete in the native archimedean
product, and its group quotient is compact. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
open OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel OAI.RepresentationTheory.Theta.Adelic.UnitaryConnected OAI.RepresentationTheory.Theta.Adelic.IntrinsicAlgebraicPlaces.Intrinsic
open OAI.RepresentationTheory.Theta.Adelic.PrincipalArithmeticIndex OAI.RepresentationTheory.Theta.Adelic.IntegralModelCongruence

variable (F : Type) [Field F] [NumberField F] (d : F)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

def nativeIntegralGroup : Subgroup (SpecialUnitary.SU H.val) :=
  (IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val)).comap (UnitaryAlgebraicModel.regularUnitaryEquiv d H.val).toMonoidHom

theorem nativeIntegralGroup_map :
    (nativeIntegralGroup F d H).map (UnitaryAlgebraicModel.regularUnitaryEquiv d H.val).toMonoidHom =
      IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val) := by
  ext g
  rw [Subgroup.mem_map_equiv]
  change UnitaryAlgebraicModel.regularUnitaryEquiv d H.val ((UnitaryAlgebraicModel.regularUnitaryEquiv d H.val).symm g) ∈
    IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val) ↔ g ∈ IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val)
  rw [MulEquiv.apply_symm_apply]

theorem native_arithmetic_presentation (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val) :
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsArithmeticPresentation (UnitaryConnected.connectedSemisimpleUnitaryGroup d H hd hH)
      (RationalSU.rationalArchimedeanSU F H) (nativeIntegralGroup F d H) := by
  refine ⟨NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F 6, UnitaryAlgebraicModel.regularUnitaryEquiv d H.val, Set.univ,
    IntrinsicAlgebraicPlaces.Intrinsic.nativeArchimedeanContinuousEquiv F d H, ?_, nativeIntegralGroup_map F d H, ?_⟩
  · intro v hv
    exact (hv (Set.mem_univ v)).elim
  · exact IntrinsicAlgebraicPlaces.Intrinsic.nativeArchimedean_diagonal F d H

theorem principal_native_commensurable (N : ℕ) (hN : 0 < N)
    (q : 𝓞 F) (hq : (q : F) = (N : F) * d) :
    (PrincipalSubgroup.principalSubgroup F d H N q hq).Commensurable (nativeIntegralGroup F d H) := by
  let e := UnitaryAlgebraicModel.regularUnitaryEquiv d H.val
  have hc := NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.commensurable_map_of_injective (PrincipalArithmeticIndex.principalModel_commensurable F d H N q hq hN)
    e.symm.toMonoidHom e.symm.injective
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro g
    exact e.symm_apply_apply g
  change (((PrincipalSubgroup.principalSubgroup F d H N q hq).map e.toMonoidHom).map e.symm.toMonoidHom).Commensurable
    ((IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val)).map e.symm.toMonoidHom) at hc
  rw [Subgroup.map_map, he, Subgroup.map_id] at hc
  have hmap : (IntegralModelCongruence.IntegralGroup (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val)).map e.symm.toMonoidHom =
      nativeIntegralGroup F d H :=
    (Subgroup.comap_equiv_eq_map_symm e _).symm
  rw [hmap] at hc
  exact hc

variable {F d H} {m : ℕ} {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

include A in
theorem principal_archimedean_compact (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val)
    (N : ℕ) (hN : 0 < N) (q : 𝓞 F) (hq : (q : F) = (N : F) * d) :
    CompactSpace (RationalSU.ArchimedeanSU F H ⧸ (PrincipalSubgroup.principalSubgroup F d H N q hq).map (RationalSU.rationalArchimedeanSU F H)) :=
  (NumberTheory.ArithmeticGroups.Lattices.Compact.CompactPlaceArithmetic.Construction.arithmetic_anisotropic_and_compact_of_compact_real_place
    (UnitaryConnected.connectedSemisimpleUnitaryGroup d H hd hH) (RationalSU.rationalArchimedeanSU F H)
    (nativeIntegralGroup F d H) (PrincipalSubgroup.principalSubgroup F d H N q hq)
    (native_arithmetic_presentation F d H hd hH) (principal_native_commensurable F d H N hN q hq)
    (IntrinsicAlgebraicPlaces.Intrinsic.unitary_compact_real_place A hd hH)).2

theorem principal_archimedean_discrete (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val)
    (N : ℕ) (hN : 0 < N) (q : 𝓞 F) (hq : (q : F) = (N : F) * d) :
    DiscreteTopology ((PrincipalSubgroup.principalSubgroup F d H N q hq).map (RationalSU.rationalArchimedeanSU F H)) :=
  NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.arithmetic_subgroup_discrete (UnitaryConnected.connectedSemisimpleUnitaryGroup d H hd hH) (RationalSU.rationalArchimedeanSU F H)
    (nativeIntegralGroup F d H) (PrincipalSubgroup.principalSubgroup F d H N q hq)
    (native_arithmetic_presentation F d H hd hH) (principal_native_commensurable F d H N hN q hq)

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalArchimedeanQuotient
