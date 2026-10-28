import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OneSidedTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.LocalRing.Length

/-! # Tor Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.TorRestriction

noncomputable section

/-! One-sided flat base change for native Tor, retaining the actual
module structure after restriction of scalars. This is the local
tensor identity needed for proper pushforward compatibility. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (N : ModuleCat.{u} S) [Module R N] [IsScalarTower R S N]

def tensorIso :
    𝟭 (ModuleCat.{u} R) ⋙ tensorLeft (.of R N) ≅
      MixedTensor.tensor R S N ⋙ ModuleCat.restrictScalars (algebraMap R S) :=
  NatIso.ofComponents (fun M =>
    (show N ⊗[R] M ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj ((MixedTensor.tensor R S N).obj M) from
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => (algebraMap_smul S r x).symm }).toModuleIso)
    (by
      intro M M' f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro n m
      rfl)

def mixedDerivedIso (M : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj (.of R N)).obj M ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (((MixedTensor.tensor R S N).leftDerived n).obj M) := by
  change ((tensorLeft (ModuleCat.of R N)).leftDerived n).obj M ≅ _
  exact DerivedBaseChange.leftDerivedIso (MixedTensor.tensor R S N) (tensorLeft (ModuleCat.of R N))
    (𝟭 _) (ModuleCat.restrictScalars (algebraMap R S)) (tensorIso R S N) M n

def iso [Module.Flat R S] (M : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj
      (((Tor (ModuleCat S) n).obj ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj N) ≅
      ((Tor (ModuleCat R) n).obj M).obj (.of R N) :=
  (ModuleCat.restrictScalars (algebraMap R S)).mapIso
      (Symmetry.iso S ((ProjectionFormula.Flat.Extension.baseChange R S).obj M) N n) ≪≫
    (ModuleCat.restrictScalars (algebraMap R S)).mapIso (OneSidedTor.derivedIso R S M N n) ≪≫
      (mixedDerivedIso R S N M n).symm ≪≫ Symmetry.iso R (.of R N) M n

theorem length [Module.Flat R S] (M : ModuleCat.{u} R) (n : ℕ) :
    Module.length R ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (((Tor (ModuleCat S) n).obj ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj N)) =
      Module.length R (((Tor (ModuleCat R) n).obj M).obj (.of R N)) :=
  (iso R S N M n).toLinearEquiv.length_eq

theorem weighted_length [Module.Flat R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M : ModuleCat.{u} R) (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) n).obj M).obj (.of R N)) =
      Module.length S (((Tor (ModuleCat S) n).obj ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj N) *
        Module.length (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  let T := ((Tor (ModuleCat S) n).obj ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj N
  let L := (ModuleCat.restrictScalars (algebraMap R S)).obj T
  let : IsScalarTower R S L := IsScalarTower.of_compHom R S T
  exact (TorRestriction.length R S N M n).symm.trans (IsLocalRing.length_restrictScalars R S L)

theorem euler [Module.Flat R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M : ModuleCat.{u} R) (d : ℕ) :
    Euler.euler R M (.of R N) d =
      Euler.euler S ((ProjectionFormula.Flat.Extension.baseChange R S).obj M) N d *
        ((Module.length (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)).toNat : ℚ) := by
  simp only [Euler.euler, ExactLength.rationalLength, weighted_length R S N,
    ENat.toNat_mul, Nat.cast_mul, ← mul_assoc, Finset.sum_mul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.TorRestriction
