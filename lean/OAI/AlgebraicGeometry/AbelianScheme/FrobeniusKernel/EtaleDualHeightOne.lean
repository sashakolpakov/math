import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightOne

/-! # Etale Dual Height One -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleDualHeightOne.Construction

noncomputable section

/-!
The Cartier dual of a reduced finite commutative p-torsion group has
height-one coordinates. This supplies the opposite multiplicative factors
directly from finite Hopf duality and reducedness of the etale coordinates.
-/

open WithConv

universe u

open OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale

section Reduced

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CharP k p]
variable [CommRing A] [Algebra k A] [IsReduced A]

include k in
/-- Over a reduced algebra of characteristic p, p-th powers are injective. -/
theorem reduced_algebra_power_injective : Function.Injective (fun a : A => a ^ p) := by
  have hp : (p : A) = 0 := by
    rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero k p, map_zero]
  let F := Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) A hp
  intro a b hab
  have hsub : (a - b) ^ p = 0 := (F.map_sub a b).trans (sub_eq_zero.mpr hab)
  exact sub_eq_zero.mp (IsNilpotent.eq_zero (show IsNilpotent (a - b) from ⟨p, hsub⟩))

end Reduced

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] [IsReduced A]

local notation "D" => OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A
local instance : CommRing D := LinearMap.convCommRing
local instance : Algebra k D := LinearMap.convAlgebra

theorem verschiebung_of_reduced_torsion
    (h : ∀ a : A, ((toConv (LinearMap.id : A →ₗ[k] A)) ^ p) a =
      algebraMap k A (Coalgebra.counit (R := k) a)) (a : A) :
    GroupSchemes.Verschiebung.FiniteEtale.verschiebungFun p k A a = algebraMap k A (Coalgebra.counit (R := k) (GroupSchemes.Verschiebung.FiniteEtale.verschiebungFun p k A a)) := by
  apply reduced_algebra_power_injective p k A
  have hv := GroupSchemes.Verschiebung.FiniteEtale.eval_verschiebung_pow p k A (1 : D) a
  have he : Coalgebra.counit (R := k) (GroupSchemes.Verschiebung.FiniteEtale.verschiebungFun p k A a) ^ p =
      Coalgebra.counit (R := k) a := by
    simpa only [one_pow, LinearMap.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply] using hv
  change GroupSchemes.Verschiebung.FiniteEtale.verschiebungFun p k A a ^ p =
    (algebraMap k A (Coalgebra.counit (R := k) (GroupSchemes.Verschiebung.FiniteEtale.verschiebungFun p k A a))) ^ p
  rw [GroupSchemes.Verschiebung.FiniteEtale.frobenius_verschiebung, h, ← map_pow, he]

/-- Reduced p-torsion coordinates dualize to height-one coordinates,
including all nilpotent functions on the Cartier dual. -/
theorem dual_heightOne_of_reduced_torsion
    (h : ∀ a : A, ((toConv (LinearMap.id : A →ₗ[k] A)) ^ p) a =
      algebraMap k A (Coalgebra.counit (R := k) a)) : HeightOneTorsion.Construction.HopfHeightOne p k D := by
  intro f
  ext a
  have hv := GroupSchemes.Verschiebung.FiniteEtale.eval_verschiebung_pow p k A (1 : D) a
  have he : Coalgebra.counit (R := k) (GroupSchemes.Verschiebung.FiniteEtale.verschiebungFun p k A a) ^ p =
      Coalgebra.counit (R := k) a := by
    simpa only [one_pow, LinearMap.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply] using hv
  have hf : f (GroupSchemes.Verschiebung.FiniteEtale.verschiebungFun p k A a) =
      Coalgebra.counit (R := k) (GroupSchemes.Verschiebung.FiniteEtale.verschiebungFun p k A a) * f 1 := by
    conv_lhs => rw [verschiebung_of_reduced_torsion p k A h a]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  change (f ^ p) a = ((Coalgebra.counit (R := k) f) ^ p) * Coalgebra.counit (R := k) a
  rw [← GroupSchemes.Verschiebung.FiniteEtale.eval_verschiebung_pow, hf, mul_pow, he]
  change Coalgebra.counit (R := k) a * f 1 ^ p = f 1 ^ p * Coalgebra.counit (R := k) a
  exact mul_comm _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleDualHeightOne.Construction
