import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimePowerProjectors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Idempotent Coordinate Group -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.IdempotentCoordinateGroup.CM

/-! The fixed subgroup of an actual idempotent on standard prime-power
torsion has standard free coordinates, with a rank to be determined by
the geometric height and Lie signature. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

variable (q n g : ℕ) (f : TorsionCoordinateMaps.CM.Criterion.coordinates q n g →* TorsionCoordinateMaps.CM.Criterion.coordinates q n g)

def additiveMap : (Fin g → ZMod (q ^ n)) →+ (Fin g → ZMod (q ^ n)) where
  toFun x := (f (Multiplicative.ofAdd x)).toAdd
  map_zero' := congrArg Multiplicative.toAdd (map_one f)
  map_add' x y := congrArg Multiplicative.toAdd
    (map_mul f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

def linearMap : Module.End (ZMod (q ^ n)) (Fin g → ZMod (q ^ n)) :=
  (additiveMap q n g f).toZModLinearMap (q ^ n)

theorem linearMap_idempotent (hf : ∀ x, f (f x) = f x) :
    linearMap q n g f * linearMap q n g f = linearMap q n g f := by
  apply LinearMap.ext
  intro x
  exact congrArg (fun z => z.toAdd) (hf (Multiplicative.ofAdd x))

def fixedRangeEquiv (hf : ∀ x, f (f x) = f x) :
    f.eqLocus (MonoidHom.id _) ≃* Multiplicative (linearMap q n g f).range where
  toFun x := Multiplicative.ofAdd ⟨x.val.toAdd, ⟨x.val.toAdd,
    congrArg Multiplicative.toAdd x.property⟩⟩
  invFun x := ⟨Multiplicative.ofAdd x.toAdd.val, by
    obtain ⟨y, hy⟩ := x.toAdd.property
    change f (Multiplicative.ofAdd x.toAdd.val) = Multiplicative.ofAdd x.toAdd.val
    rw [← hy]
    exact hf (Multiplicative.ofAdd y)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem exists_fixed_coordinates [Fact q.Prime] (r : ℕ)
    (a : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) r →* TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) r)
    (ha : ∀ x, a (a x) = a x) :
    ∃ d : ℕ, Nonempty (a.eqLocus (MonoidHom.id _) ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) d) := by
  let p := linearMap q (n + 1) r a
  let : Fact (1 < q ^ (n + 1)) := ⟨one_lt_pow' (Fact.out : q.Prime).one_lt (Nat.succ_ne_zero n)⟩
  let : Module.Free (ZMod (q ^ (n + 1))) p.range :=
    PrimePowerProjectors.CM.projector_range_free q n r p (linearMap_idempotent q (n + 1) r a ha)
  let e := (Module.finBasis (ZMod (q ^ (n + 1))) p.range).equivFun
  exact ⟨Module.finrank (ZMod (q ^ (n + 1))) p.range,
    ⟨(fixedRangeEquiv q (n + 1) r a ha).trans e.toAddEquiv.toMultiplicative⟩⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.IdempotentCoordinateGroup.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.IdempotentCoordinateGroup.CM.RetractCoordinates

/-! An actual group retract of free prime-power torsion has standard
coordinates. Its idempotent and its fixed subgroup are constructed from
the given inclusion and retraction. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

variable {A B : Type*} [CommGroup A] [CommGroup B]
  (r : A →* B) (s : B →* A) (hrs : ∀ b, r (s b) = b)
  (q n g : ℕ) (e : A ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q n g)

def projector : TorsionCoordinateMaps.CM.Criterion.coordinates q n g →* TorsionCoordinateMaps.CM.Criterion.coordinates q n g :=
  e.toMonoidHom.comp (s.comp (r.comp e.symm.toMonoidHom))

include hrs in
theorem projector_idempotent (x : TorsionCoordinateMaps.CM.Criterion.coordinates q n g) :
    projector r s q n g e (projector r s q n g e x) = projector r s q n g e x := by
  change e (s (r (e.symm (e (s (r (e.symm x))))))) = e (s (r (e.symm x)))
  rw [e.symm_apply_apply, hrs]

def fixedEquiv : B ≃* (projector r s q n g e).eqLocus (MonoidHom.id _) where
  toFun b := ⟨e (s b), by
    change e (s (r (e.symm (e (s b))))) = e (s b)
    rw [e.symm_apply_apply, hrs]⟩
  invFun x := r (e.symm x.val)
  left_inv b := by change r (e.symm (e (s b))) = b; rw [e.symm_apply_apply, hrs]
  right_inv x := Subtype.ext x.property
  map_mul' x y := Subtype.ext (by change e (s (x * y)) = e (s x) * e (s y); rw [map_mul, map_mul])

include hrs in
theorem exists_coordinates [Fact q.Prime] (m : ℕ)
    (c : A ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q (m + 1) g) :
    ∃ d : ℕ, Nonempty (B ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q (m + 1) d) := by
  obtain ⟨d, ⟨a⟩⟩ := exists_fixed_coordinates q m g
    (projector r s q (m + 1) g c) (projector_idempotent r s hrs q (m + 1) g c)
  exact ⟨d, ⟨(fixedEquiv r s hrs q (m + 1) g c).trans a⟩⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.IdempotentCoordinateGroup.CM.RetractCoordinates

end

end OAI
