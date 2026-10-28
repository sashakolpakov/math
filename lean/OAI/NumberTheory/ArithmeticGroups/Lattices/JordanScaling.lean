import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingScalarDescent

/-! # Jordan Scaling -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.JordanScaling.Construction

noncomputable section

section

/-! In a Killing Lie algebra, an element with nilpotent adjoint action
admits a rational infinitesimal scaling element. This is the first
step toward excluding rational nilpotents using anisotropy. -/

open scoped Classical
open LieAlgebra

attribute [local instance] LieRing.ofAssociativeRing

theorem killing_orthogonal_range_ad
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]
    [Module.Finite k L] [LieAlgebra.IsKilling k L] (e : L) :
    (killingForm k L).orthogonal (ad k L e).range = (ad k L e).ker := by
  ext x
  constructor
  · intro hx
    have hz : killingForm k L ⁅e, x⁆ = 0 := by
      apply LinearMap.ext
      intro y
      have h := hx (⁅e, y⁆) ⟨y, rfl⟩
      rw [LieModule.traceForm_apply_lie_apply'] at h
      change killingForm k L ⁅e, x⁆ y = 0
      rw [LieModule.traceForm_comm]
      exact neg_eq_zero.mp h
    have hker : ⁅e, x⁆ ∈ LinearMap.ker (killingForm k L) := hz
    change ⁅e, x⁆ = 0
    simpa only [LieAlgebra.IsKilling.ker_killingForm_eq_bot, Submodule.mem_bot] using hker
  · intro hx
    rintro y ⟨z, rfl⟩
    change killingForm k L ⁅e, z⁆ x = 0
    rw [LieModule.traceForm_apply_lie_apply']
    change -killingForm k L z ((ad k L e) x) = 0
    rw [hx, map_zero, neg_zero]

theorem nilpotent_mem_orthogonal_ad_kernel
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    (e : L) (he : _root_.IsNilpotent (ad k L e : Module.End k L)) :
    e ∈ (killingForm k L).orthogonal (ad k L e).ker := by
  intro z hz
  have hbracket : ⁅e, z⁆ = 0 := hz
  have hcomm : Commute (ad k L e : Module.End k L) (ad k L z) := by
    have h := (ad k L).map_lie e z
    rw [hbracket, map_zero] at h
    exact (sub_eq_zero.mp h.symm : _)
  rw [LieModule.traceForm_comm]
  change LinearMap.trace k L (ad k L e * ad k L z) = 0
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (hcomm.isNilpotent_mul_right he)).eq_zero

theorem exists_lie_eq_self_of_nilpotent_ad
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]
    [Module.Finite k L] [LieAlgebra.IsKilling k L]
    (e : L) (he : _root_.IsNilpotent (ad k L e : Module.End k L)) :
    ∃ h : L, ⁅h, e⁆ = e := by
  have hm := nilpotent_mem_orthogonal_ad_kernel e he
  rw [← killing_orthogonal_range_ad e,
    LinearMap.BilinForm.orthogonal_orthogonal (LieAlgebra.IsKilling.killingForm_nondegenerate k L)
      (LieModule.traceForm_isSymm k L L).isRefl] at hm
  obtain ⟨h, hh⟩ := hm
  refine ⟨-h, ?_⟩
  rw [neg_lie, lie_skew]
  exact hh

theorem infinitesimal_nilpotent_has_scaling_matrix
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n)
    (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hnil : _root_.IsNilpotent A) :
    ∃ H ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, H * A - A * H = A := by
  let : LieAlgebra.IsKilling k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := KillingScalarDescent.Construction.infinitesimal_isKilling G hconn hsemi
  let e : Infinitesimal.Action.Construction.infinitesimalStabilizer G := ⟨A, hA⟩
  have he : _root_.IsNilpotent (ad k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) e) :=
    LieAlgebra.isNilpotent_ad_of_isNilpotent hnil
  obtain ⟨H, hH⟩ := exists_lie_eq_self_of_nilpotent_ad e he
  refine ⟨H.val, H.property, ?_⟩
  exact congrArg (fun x : Infinitesimal.Action.Construction.infinitesimalStabilizer G => x.val) hH

end

/-! The semisimple summand of a Jordan decomposition retains every
eigenvector and hence every infinitesimal scaling relation. -/

open scoped Classical
open _root_.Module LieAlgebra

theorem semisimple_summand_on_eigenvector
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (N S : Module.End k V) (hNS : Commute N S) (hN : _root_.IsNilpotent N)
    (hS : S.IsSemisimple) (x : V) (a : k) (hx : (N + S) x = a • x) :
    S x = a • x ∧ N x = 0 := by
  have hmem : x ∈ (N + S).genEigenspace a 1 := Module.End.mem_eigenspace_iff.mpr hx
  have hsx : S x = a • x :=
    Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hmem
      (hNS.add_left (Commute.refl S)) hS.isFinitelySemisimple (by simpa only [add_sub_cancel_right] using hN)
  refine ⟨hsx, ?_⟩
  change N x + S x = a • x at hx
  rw [hsx] at hx
  exact add_eq_right.mp hx

attribute [local instance] LieRing.ofAssociativeRing

theorem semisimple_summand_retains_bracket_scaling
    {k V : Type*} [Field k] [PerfectField k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (N S A : Module.End k V) (hNS : Commute N S) (hN : _root_.IsNilpotent N)
    (hS : S.IsSemisimple) (a : k) (hscale : ⁅N + S, A⁆ = a • A) :
    ⁅S, A⁆ = a • A ∧ ⁅N, A⁆ = 0 := by
  apply semisimple_summand_on_eigenvector (ad k _ N) (ad k _ S)
    (LieAlgebra.commute_ad_of_commute hNS) (LieAlgebra.ad_nilpotent_of_nilpotent hN)
    (LieAlgebra.ad_isSemisimple_of_isSemisimple hS) A a
  rw [← map_add]
  exact hscale

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.JordanScaling.Construction
