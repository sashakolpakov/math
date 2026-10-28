import OAI.AlgebraicGeometry.CycleClass.Thom.Local.ParameterMap
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # DVR Formal Smooth -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.DVRFormalSmooth.Constructions

noncomputable section

/-! A discrete valuation ring essentially of finite type over a
characteristic-zero field is formally smooth over that field. -/

open _root_.Algebra _root_.Polynomial IsLocalRing

open OAI.AlgebraicGeometry.CycleClass.Thom.Local.ParameterMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmoothLocalFiber.Constructions

theorem formallySmooth (k R : Type*) [Field k] [CharZero k]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra k R] [Algebra.EssFiniteType k R] : Algebra.FormallySmooth k R := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  let A := Local.ParameterMap.Constructions.parameterStalk k R t
  let : Algebra A R := (Local.ParameterMap.Constructions.parameterMap k R t).toRingHom.toAlgebra
  let : IsScalarTower k A R := IsScalarTower.of_algebraMap_eq'
    (Local.ParameterMap.Constructions.parameterMap k R t).comp_algebraMap.symm
  let : IsLocalHom (algebraMap A R) := Local.ParameterMap.Constructions.parameterMap_isLocalHom k R t
  let : Module.IsTorsionFree A R := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (Local.ParameterMap.Constructions.parameterMap_injective k R t ht.ne_zero ht.not_isUnit)
  let : Module.Flat A R := inferInstance
  let : Algebra.EssFiniteType A R := Algebra.EssFiniteType.of_comp k A R
  let : CharZero (ResidueField A) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField A)).injective
  have hm : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R :=
    (Local.ParameterMap.Constructions.parameterMap_maximalIdeal k R t ht.not_isUnit).trans
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht).symm
  let : Algebra.FormallySmooth A R := SmoothLocalFiber.Constructions.formallySmooth_of_maximalIdeal_map A R hm
  let : Algebra.FormallySmooth k A := Algebra.FormallySmooth.comp k k[X] A
  exact Algebra.FormallySmooth.comp k A R

end

end OAI.AlgebraicGeometry.CycleClass.Thom.DVRFormalSmooth.Constructions
