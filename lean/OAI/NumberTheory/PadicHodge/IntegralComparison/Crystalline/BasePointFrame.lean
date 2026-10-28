import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Nilpotence

/-! # Base Point Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BasePointFrame

noncomputable section

/-! The actual truncated Witt base is a terminal frame in the original bounded crystalline site of the base field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]

def baseMap : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (WittVector p k)) :=
  Witt.Crystalline.wittStructureMap p k (Over.mk (𝟙 (Spec (CommRingCat.of k))))

omit [Fintype k] [CharP k p] in
theorem baseMap_eq : baseMap p k = Spec.map (CommRingCat.ofHom WittVector.constantCoeff) :=
  Category.id_comp _

instance baseMap_mono : Mono (baseMap p k) := by
  rw [baseMap_eq]
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (WittVector.constantCoeff : WittVector p k →+* k))) :=
    IsClosedImmersion.spec_of_surjective _ (WittVector.constantCoeff_surjective p)
  infer_instance

variable (n : ℕ)

def residueEquiv : (Truncated.Witt.Ring p k n ⧸ Truncated.Witt.ideal p k n) ≃+* k :=
  (Ideal.quotEquivOfEq (Truncated.Witt.reduction_kernel p k n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (Truncated.Witt.reduction_surjective p k n))

theorem residueEquiv_mk (w : Truncated.Witt.Ring p k n) :
    residueEquiv p k n (Ideal.Quotient.mk (Truncated.Witt.ideal p k n) w) =
      Truncated.Witt.reduction p k n w := by
  change (RingHom.quotientKerEquivOfSurjective (Truncated.Witt.reduction_surjective p k n))
    ((Ideal.quotEquivOfEq (Truncated.Witt.reduction_kernel p k n).symm)
      (Ideal.Quotient.mk (Truncated.Witt.ideal p k n) w)) = _
  rw [Ideal.quotEquivOfEq_mk]
  rfl

def object : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (baseMap p k) where
  ring := CommRingCat.of (Truncated.Witt.Ring p k n)
  base := Truncated.Witt.quotient p k n
  ideal := Truncated.Witt.ideal p k n
  dividedPowers := Truncated.Witt.dividedPowers p k n
  baseCompatible := Truncated.Witt.quotient_isDPMorphism p k n
  primeNilpotent := Truncated.Witt.prime_nilpotent p k n
  nilIdeal := fun _ hx => DividedPower.Nilpotence.nilpotent_of_mem
    (Truncated.Witt.dividedPowers p k n) p (Fact.out : p.Prime).pos
      (Truncated.Witt.prime_nilpotent p k n) hx
  mapToX := Spec.map (CommRingCat.ofHom (residueEquiv p k n).symm.toRingHom)
  overBase := by
    rw [baseMap_eq, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    apply (residueEquiv p k n).injective
    change residueEquiv p k n ((residueEquiv p k n).symm (WittVector.constantCoeff w)) =
      residueEquiv p k n (Ideal.Quotient.mk (Truncated.Witt.ideal p k n)
        (Truncated.Witt.quotient p k n w))
    rw [RingEquiv.apply_symm_apply, residueEquiv_mk]
    rfl

def bounded : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (baseMap p k) n :=
  ⟨object p k n, Truncated.Witt.prime_power_zero p k n⟩

variable (U : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (baseMap p k) n)

def ringMap : DividedPowers.DPMorphism (object p k n).dividedPowers U.obj.dividedPowers :=
  { toRingHom := Bounded.WittBase.truncatedBase p k U.obj n U.property
    __ := Bounded.WittBase.truncatedBase_isDPMorphism p k U.obj n U.property }

theorem overBase : (BasePointFrame.ringMap p k n U).toRingHom.comp (object p k n).base = U.obj.base :=
  Bounded.WittBase.truncatedBase_quotient p k U.obj n U.property

theorem overX :
    Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U.obj (object p k n) (BasePointFrame.ringMap p k n U))) ≫
      (object p k n).mapToX = U.obj.mapToX := by
  apply (cancel_mono (baseMap p k)).mp
  rw [Category.assoc, (object p k n).overBase, U.obj.overBase]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

def toBase : U ⟶ bounded p k n :=
  ObjectProperty.homMk
    { ringMap := BasePointFrame.ringMap p k n U
      overBase := BasePointFrame.overBase p k n U
      overX := BasePointFrame.overX p k n U }

theorem unique (g : U ⟶ bounded p k n) : g = toBase p k n U := by
  apply ObjectProperty.hom_ext
  apply BigCrystallineSite.Object.Hom.ext
  apply DividedPowers.DPMorphism.ext
  funext x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (fun h => h w) g.hom.overBase

def isTerminal : IsTerminal (bounded p k n) :=
  IsTerminal.ofUniqueHom (toBase p k n) (fun U g => unique p k n U g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BasePointFrame
