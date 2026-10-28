import OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder
import OAI.RepresentationTheory.Theta.Adelic.SubringCongruence

/-! # Principal Subgroup -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup

noncomputable section

/-! The literal coefficient congruence condition in AdelicTheta defines a
subgroup after the chosen integer clears the quadratic denominator. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder OAI.RepresentationTheory.Theta.Adelic.SubringCongruence

def suSpecialLinear {R J : Type*} [CommRing R] [StarRing R]
    [Fintype J] [DecidableEq J] (H : Matrix J J R) :
    SpecialUnitary.SU H →* Matrix.SpecialLinearGroup J R where
  toFun g := ⟨g.val.val, congrArg Units.val g.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (F : Type) [Field F] [NumberField F] (d : F)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (N : ℕ) (q : 𝓞 F) (hq : (q : F) = (N : F) * d)

def principalSubgroup : Subgroup (SpecialUnitary.SU H.val) :=
  (SubringCongruence.congruenceImage (PrincipalCoefficientOrder.coefficientOrder F d N q hq) (PrincipalCoefficientOrder.coefficientIdeal F d N q hq)).comap
    (suSpecialLinear H.val)

def principalCoefficient (a b : 𝓞 F) : PrincipalCoefficientOrder.coefficientOrder F d N q hq :=
  ⟨(N : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) * (⟨(a : F), (b : F)⟩ : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d),
    ⟨N * a, b, by ext <;> simp⟩⟩

omit [NumberField F] in
theorem principalSubgroup_mem_iff (g : SpecialUnitary.SU H.val) :
    g ∈ principalSubgroup F d H N q hq ↔ BallGeometryData.PrincipalLevel N g := by
  change suSpecialLinear H.val g ∈
    SubringCongruence.congruenceImage (PrincipalCoefficientOrder.coefficientOrder F d N q hq) (PrincipalCoefficientOrder.coefficientIdeal F d N q hq) ↔ _
  rw [SubringCongruence.congruenceImage_mem_iff]
  constructor
  · intro hg i j
    obtain ⟨x, hx, he⟩ := hg i j
    obtain ⟨a, b, hab⟩ := (PrincipalCoefficientOrder.coefficientIdeal_membership F d N q hq x).mp hx
    exact ⟨a, b, he.trans hab⟩
  · intro hg i j
    obtain ⟨a, b, hab⟩ := hg i j
    refine ⟨principalCoefficient F d N q hq a b, ?_, hab⟩
    exact (PrincipalCoefficientOrder.coefficientIdeal_membership F d N q hq _).mpr ⟨a, b, rfl⟩

omit [NumberField F] in
include q hq in
theorem principalLevel_inv (g : SpecialUnitary.SU H.val) (hg : BallGeometryData.PrincipalLevel N g) :
    BallGeometryData.PrincipalLevel N g⁻¹ :=
  (principalSubgroup_mem_iff F d H N q hq g⁻¹).mp
    ((principalSubgroup F d H N q hq).inv_mem
      ((principalSubgroup_mem_iff F d H N q hq g).mpr hg))

omit [NumberField F] in
include q hq in
theorem principalLevel_mul (g h : SpecialUnitary.SU H.val) (hg : BallGeometryData.PrincipalLevel N g) (hh : BallGeometryData.PrincipalLevel N h) :
    BallGeometryData.PrincipalLevel N (g * h) :=
  (principalSubgroup_mem_iff F d H N q hq (g * h)).mp
    ((principalSubgroup F d H N q hq).mul_mem
      ((principalSubgroup_mem_iff F d H N q hq g).mpr hg)
      ((principalSubgroup_mem_iff F d H N q hq h).mpr hh))

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
