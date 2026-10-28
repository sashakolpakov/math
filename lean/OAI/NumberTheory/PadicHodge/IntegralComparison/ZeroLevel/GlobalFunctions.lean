import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.AffineOpenSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Global Functions -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalFunctions

noncomputable section

/-! Original crystalline section values glue to actual global regular functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.AffineOpenSections

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom]

omit p [Fact p.Prime] [CharP k p] in
theorem affine_inf {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) :=
  (isAffineHom_diagonal_iff (f := X.hom)).mp (inferInstance : IsAffineHom (pullback.diagonal X.hom))
    ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

theorem exists_unique (s : AffineOpenSections.Sections p k X) :
    ∃! a : Γ(X.left, ⊤), ∀ (U : X.left.Opens) (hU : IsAffineOpen U),
      X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a = AffineOpenSections.value p k X s U hU := by
  let V : X.left.affineOpens → X.left.Opens := fun U => U.val
  let a (U : X.left.affineOpens) := AffineOpenSections.value p k X s U.val U.property
  have ha : TopCat.Presheaf.IsCompatible X.left.presheaf V a := by
    intro U W
    exact (AffineOpenSections.restriction p k X s inf_le_left U.property (affine_inf k X U.property W.property)).trans
      (AffineOpenSections.restriction p k X s inf_le_right W.property (affine_inf k X U.property W.property)).symm
  obtain ⟨b, hb, hu⟩ := X.left.sheaf.existsUnique_gluing' V ⊤ (fun _ => homOfLE le_top)
    (iSup_affineOpens_eq_top X.left).ge a ha
  refine ⟨b, fun U hU => hb ⟨U, hU⟩, ?_⟩
  intro c hc
  exact hu c (fun U => hc U.val U.property)

def value (s : AffineOpenSections.Sections p k X) : Γ(X.left, ⊤) := (exists_unique p k X s).choose

theorem restriction (s : AffineOpenSections.Sections p k X) (U : X.left.Opens) (hU : IsAffineOpen U) :
    X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (value p k X s) =
      AffineOpenSections.value p k X s U hU :=
  (exists_unique p k X s).choose_spec.1 U hU

theorem unique (s : AffineOpenSections.Sections p k X) (a : Γ(X.left, ⊤))
    (h : ∀ (U : X.left.Opens) (hU : IsAffineOpen U),
      X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a =
        AffineOpenSections.value p k X s U hU) : a = value p k X s :=
  (exists_unique p k X s).choose_spec.2 a h

theorem value_add (s t : AffineOpenSections.Sections p k X) : value p k X (s + t) = value p k X s + value p k X t := by
  symm
  apply unique p k X
  intro U hU
  rw [map_add, restriction, restriction, AffineOpenSections.value_add]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalFunctions
