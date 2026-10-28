import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTupleValues
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison

/-! # Cech Differential Values -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechDifferentialValues

noncomputable section

/-! The Cech differential is the alternating sum of restrictions, on each
tuple and after restriction to any smaller open. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechTupleCoordinates

private theorem sum_apply {R : Type u} [CommRing R] {A B : ModuleCat.{u} R}
    {I : Type*} [Fintype I] (v : I → (A ⟶ B)) (x : A) :
    (∑ i, v i) x = ∑ i, v i x := by
  change (∑ i, v i).hom x = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]

private theorem zsmul_apply {R : Type u} [CommRing R] {A B : ModuleCat.{u} R}
    (n : ℤ) (v : A ⟶ B) (x : A) : (n • v) x = n • v x := rfl

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

def delete (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2)) : Fin (q + 1) → ι :=
  a ∘ (SimplexCategory.δ k).toOrderHom.toFun

def face (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    (∏ᶜ fun j => U (a j)) ⟶ ∏ᶜ fun j => U (delete q a k j) :=
  ((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ a

theorem differential_value (q : ℕ) (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X q) (a : Fin (q + 2) → ι) :
    CechTupleValues.Construction.CechTupleCoordinates.value π M U (q + 1) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d q (q + 1) z) a =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        M.presheaf.map (face U q a k).op (CechTupleValues.Construction.CechTupleCoordinates.value π M U q z (delete q a k)) := by
  have h := ConcreteCategory.congr_hom (SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechComplex_d_comp_π π M U q a) z
  rw [CechTupleCoordinates.sum_apply] at h
  simp only [zsmul_apply, ModuleCat.comp_apply] at h
  exact h

def restrictedValue (q : ℕ) (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X q)
    (a : Fin (q + 1) → ι) (W : X.Opens) (hW : W ≤ ∏ᶜ fun j => U (a j)) : Γ(M, W) :=
  M.presheaf.map (homOfLE hW).op (CechTupleValues.Construction.CechTupleCoordinates.value π M U q z a)

theorem restricted_index (q : ℕ) (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X q)
    (a b : Fin (q + 1) → ι) (hab : a = b) (W : X.Opens)
    (ha : W ≤ ∏ᶜ fun j => U (a j)) (hb : W ≤ ∏ᶜ fun j => U (b j)) :
    restrictedValue π M U q z a W ha = restrictedValue π M U q z b W hb := by
  subst b
  rfl

theorem restricted_differential (q : ℕ) (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X q)
    (a : Fin (q + 2) → ι) (W : X.Opens) (hW : W ≤ ∏ᶜ fun j => U (a j)) :
    restrictedValue π M U (q + 1) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d q (q + 1) z) a W hW =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        restrictedValue π M U q z (delete q a k) W
          (hW.trans (leOfHom (face U q a k))) := by
  unfold restrictedValue
  rw [differential_value, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul, ← M.presheaf.map_comp_apply]
  rfl

end Construction.CechTupleCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechDifferentialValues
