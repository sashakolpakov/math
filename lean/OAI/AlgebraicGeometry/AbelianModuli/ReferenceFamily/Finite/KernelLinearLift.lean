import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearDescent
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Kernel Linear Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.KernelLinearLift

noncomputable section

/-! A finite kernel on the genuine torus quotient forces injectivity
of its complex linear lift. The linear kernel is connected, whereas
both the finite quotient kernel and the period lattice are discrete. -/

open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction

theorem linearLift_injective_of_finite_kernel (A B : Geometry.ComplexTorus.BettiLattice.CM.Construction.Torus)
    (f : A.Point →+ B.Point) (L : A.V →ₗ[ℂ] B.V) (hL : Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts f L)
    (hfinite : {q : A.Point | f q = 0}.Finite) : Function.Injective L := by
  let : DiscreteTopology A.lattice.toAddSubgroup := A.discrete
  let : IsClosed (A.lattice.toAddSubgroup : Set A.V) := AddSubgroup.isClosed_of_discreteTopology
  let : T1Space A.Point := inferInstanceAs (T1Space (A.V ⧸ A.lattice.toAddSubgroup))
  let K := L.ker
  let q : K → A.Point := fun v => A.proj v.val
  have hq : Continuous q := QuotientAddGroup.continuous_mk.comp continuous_subtype_val
  have hm : Set.MapsTo q Set.univ {x : A.Point | f x = 0} := by
    intro v _
    exact (hL v.val).trans ((congrArg B.proj v.property).trans (QuotientAddGroup.mk_zero _))
  have hzero (v : K) : q v = 0 := by
    have he : q v = q 0 := isPreconnected_univ.constant_of_mapsTo hfinite.isDiscrete hq.continuousOn hm trivial trivial
    exact he.trans (QuotientAddGroup.mk_zero _)
  have hk (v : K) : v.val ∈ A.lattice := (QuotientAddGroup.eq_zero_iff v.val).mp (hzero v)
  have hdisc : IsDiscrete (A.lattice : Set A.V) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  exact isPreconnected_univ.constant_of_mapsTo hdisc continuous_subtype_val.continuousOn
    (fun x _ => hk x) (x := (⟨v, hv⟩ : K)) (y := (0 : K)) trivial trivial

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.KernelLinearLift
