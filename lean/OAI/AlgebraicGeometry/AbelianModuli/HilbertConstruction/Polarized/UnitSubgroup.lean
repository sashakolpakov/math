import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.UnitFaithfulness

/-! # Unit Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual endomorphism-ring units of polarized full-level automorphisms form a subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}

theorem Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_refl : (Moduli.Isomorphisms.LevelPreservingIso.refl A).endRingUnit = 1 := by
  apply Units.ext
  apply Additive.toMul.injective
  apply Grp.hom_ext
  rfl

theorem Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_trans (e f : Moduli.Isomorphisms.LevelPreservingIso A A) :
    (e.trans f).endRingUnit = f.endRingUnit * e.endRingUnit := by
  apply Units.ext
  apply Additive.toMul.injective
  apply Grp.hom_ext
  rfl

theorem Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_symm (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    e.symm.endRingUnit = e.endRingUnit⁻¹ := by
  apply Units.ext
  apply Additive.toMul.injective
  apply Grp.hom_ext
  rfl

def PolarizationData.PolarizedAbelianWithFullLevel.automorphismUnitSubgroup (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    Subgroup A.abelian.EndRingˣ where
  carrier := Set.range Moduli.Isomorphisms.LevelPreservingIso.endRingUnit
  one_mem' := ⟨Moduli.Isomorphisms.LevelPreservingIso.refl A, Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_refl⟩
  mul_mem' := by
    rintro _ _ ⟨e, rfl⟩ ⟨f, rfl⟩
    exact ⟨f.trans e, f.endRingUnit_trans e⟩
  inv_mem' := by
    rintro _ ⟨e, rfl⟩
    exact ⟨e.symm, e.endRingUnit_symm⟩

def Moduli.Isomorphisms.LevelPreservingIso.automorphismUnit (e : Moduli.Isomorphisms.LevelPreservingIso A A) : A.automorphismUnitSubgroup :=
  ⟨e.endRingUnit, ⟨e, rfl⟩⟩

theorem Moduli.Isomorphisms.LevelPreservingIso.automorphismUnit_surjective :
    Function.Surjective (Moduli.Isomorphisms.LevelPreservingIso.automorphismUnit (A := A)) := by
  rintro ⟨_, e, rfl⟩
  exact ⟨e, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
