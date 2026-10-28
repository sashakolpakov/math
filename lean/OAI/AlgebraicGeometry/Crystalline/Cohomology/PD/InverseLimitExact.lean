import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimitUniversal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SequentialModule

/-! # Inverse Limit Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimitExact.PDInverseLimitExact

noncomputable section

/-!
# The exact difference sequence for the original PD inverse limit

The existing completed PD ring is the kernel of the successive difference
map on the product of the actual thickening rings. Surjective successive
transitions make this an explicit short exact sequence of Witt modules.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (F : ℕᵒᵖ ⥤ Thickening.AffinePDThickening p k B)

local notation "W" => WittVector p k
abbrev LevelRing (n : ℕ) : Type u := (F.obj (op n)).ring

local notation "M" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimitExact.PDInverseLimitExact.LevelRing p k B F

def successive (n : ℕ) : M (n + 1) →ₗ[W] M n :=
  (InverseLimit.PDInverseLimit.transition p k B F n (n + 1) (Nat.le_succ n)).hom.toLinearMap

theorem compatible_of_successive (x : ∀ n, M n)
    (hx : ∀ n, successive p k B F n (x (n + 1)) = x n) :
    ∀ n m h, (InverseLimit.PDInverseLimit.transition p k B F n m h).hom (x m) = x n := by
  intro n m h
  induction m, h using Nat.le_induction with
  | base =>
      exact congrArg (fun f => f.hom (x n)) (F.map_id (op n))
  | succ m h ih =>
      have hc := congrArg (fun f => f.hom (x (m + 1)))
        (F.map_comp (homOfLE (Nat.le_succ m)).op (homOfLE h).op)
      exact hc.trans ((congrArg (InverseLimit.PDInverseLimit.transition p k B F n m h).hom (hx m)).trans ih)

def difference : (∀ n, M n) →ₗ[W] (∀ n, M n) :=
  SequentialModule.SequentialModuleDifference.difference W M (successive p k B F)

def inclusion : InverseLimit.PDInverseLimit.Ring p k B F →ₗ[W] (∀ n, M n) where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem difference_inclusion : (difference p k B F).comp (inclusion p k B F) = 0 := by
  ext x n
  exact sub_eq_zero.mpr (x.property n (n + 1) (Nat.le_succ n)).symm

def sequence : ShortComplex (ModuleCat.{u} W) :=
  ShortComplex.mk (ModuleCat.ofHom (inclusion p k B F)) (ModuleCat.ofHom (difference p k B F))
    (ModuleCat.hom_ext (difference_inclusion p k B F))

theorem exact : (sequence p k B F).Exact := by
  apply (ShortComplex.moduleCat_exact_iff (sequence p k B F)).mpr
  intro x hx
  have hc : ∀ n, successive p k B F n (x (n + 1)) = x n := by
    intro n
    exact (sub_eq_zero.mp (congrFun hx n)).symm
  exact ⟨⟨x, compatible_of_successive p k B F x hc⟩, rfl⟩

instance inclusion_mono : Mono (sequence p k B F).f :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

theorem shortExact (hF : ∀ n, Function.Surjective (successive p k B F n)) :
    (sequence p k B F).ShortExact where
  exact := PDInverseLimitExact.exact p k B F
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (SequentialModule.SequentialModuleDifference.surjective W M (successive p k B F) hF)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimitExact.PDInverseLimitExact
