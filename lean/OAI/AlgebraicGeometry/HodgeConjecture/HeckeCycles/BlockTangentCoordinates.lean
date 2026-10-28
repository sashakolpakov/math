import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionGenerators
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks

/-! # Block Tangent Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockTangentCoordinates.CM

noncomputable section

/-! Linear coordinates for additive characters of the literal standard
q-power block labels, obtained by evaluating the coordinate generators. -/

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

variable (k : Type) [Field k] (q n d : ℕ) [Fact q.Prime] [CharP k q]

def residueCast : ZMod (q ^ (n + 1)) →+* k :=
  ZMod.castHom (dvd_pow_self q (Nat.succ_ne_zero n)) k

def label (i : Fin d) : Additive (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) d) :=
  Additive.ofMul (ULift.up (TorsionGenerators.CM.generator q (n + 1) d i))

def evaluation : (Additive (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) d) →+ k) →ₗ[k] (Fin d → k) where
  toFun f i := f (label q n d i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def character (c : Fin d → k) : Additive (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) d) →+ k where
  toFun x := ∑ i, residueCast k q n (x.toMul.down.toAdd i) * c i
  map_zero' := by simp
  map_add' x y := by
    change (∑ i, residueCast k q n (x.toMul.down.toAdd i + y.toMul.down.toAdd i) * c i) = _
    simp only [map_add, add_mul, Finset.sum_add_distrib]

omit [Fact q.Prime] in
theorem evaluation_character (c : Fin d → k) : evaluation k q n d (character k q n d c) = c := by
  classical
  funext i
  simp [evaluation, character, label, TorsionGenerators.CM.generator, Pi.single_apply]

def asGroupHom (f : Additive (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) d) →+ k) :
    TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) d →* Multiplicative k where
  toFun x := Multiplicative.ofAdd (f (Additive.ofMul (ULift.up x)))
  map_one' := congrArg Multiplicative.ofAdd (map_zero f)
  map_mul' x y := congrArg Multiplicative.ofAdd
    (map_add f (Additive.ofMul (ULift.up x)) (Additive.ofMul (ULift.up y)))

omit [CharP k q] in
theorem evaluation_injective : Function.Injective (evaluation k q n d) := by
  intro f h he
  have hm := TorsionGenerators.CM.hom_ext q (n + 1) d (Fact.out : q.Prime).ne_zero
    (asGroupHom k q n d f) (asGroupHom k q n d h)
    (fun i => congrArg Multiplicative.ofAdd (congrFun he i))
  apply AddMonoidHom.ext
  intro x
  exact congrArg (fun a : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) d →* Multiplicative k =>
    (a x.toMul.down).toAdd) hm

def characterEquiv : (Additive (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) d) →+ k) ≃ₗ[k] (Fin d → k) :=
  LinearEquiv.ofBijective (evaluation k q n d)
    ⟨evaluation_injective k q n d, fun c => ⟨character k q n d c, evaluation_character k q n d c⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockTangentCoordinates.CM
