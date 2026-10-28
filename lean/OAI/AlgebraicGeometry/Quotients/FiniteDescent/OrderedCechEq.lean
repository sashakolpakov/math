import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare

/-! # Ordered Cech Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq

noncomputable section

/-! Compatible local sections represented by an ordered Cech zero-cycle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrderedCechZeroCoordinates

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

abbrev intersection (q : ℕ) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) : X.Opens := ∏ᶜ fun k => U (a.1 k)

def single (i : ι) : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 := ⟨fun _ => i, by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro k
    exact Fin.elim0 k⟩

def pair (i j : ι) (h : i < j) : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1 :=
  ⟨![i, j], by apply Fin.strictMono_iff_lt_succ.mpr; intro k; fin_cases k; exact h⟩

theorem single_of_index (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) : single (a.1 0) = a := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

theorem pair_delete_zero (i j : ι) (h : i < j) : (pair i j h).delete 0 = single j := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

theorem pair_delete_one (i j : ι) (h : i < j) : (pair i j h).delete 1 = single i := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

theorem single_open (i : ι) : intersection U 0 (single i) = U i := by
  apply le_antisymm
  · exact leOfHom (Pi.π (fun _ : Fin 1 => U i) 0)
  · exact leOfHom (Pi.lift fun _ : Fin 1 => 𝟙 (U i))

theorem pair_open (i j : ι) (h : i < j) : intersection U 1 (pair i j h) = U i ⊓ U j := by
  apply le_antisymm
  · exact le_inf (leOfHom (Pi.π _ 0)) (leOfHom (Pi.π _ 1))
  · apply leOfHom
    refine Pi.lift (fun k : Fin 2 => homOfLE ?_)
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

abbrev cycles := ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.ker

def value (s : cycles π M U) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) : Γ(M, intersection U 0 a) :=
  Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 j.1) a s.val

private theorem alternating_two {A : Type*} [AddCommGroup A] (v : Fin 2 → A) :
    (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • v k) = v 0 - v 1 := by
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul, sub_eq_add_neg]

theorem differential_zero : (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1 =
    SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0 0 - SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0 1 :=
  alternating_two (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0)

theorem cofaces_eq (s : cycles π M U) :
    SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0 0 s.val = SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0 1 s.val := by
  have h := s.property
  change (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1 s.val = 0 at h
  rw [differential_zero] at h
  exact sub_eq_zero.mp h

def face (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1) (k : Fin 2) :
    intersection U 1 a ⟶ intersection U 0 (a.delete k) := (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedCechFace U 0 k).φ a

theorem coface_value (s : cycles π M U) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1) (k : Fin 2) :
    Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 1 j.1) a
      (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0 k s.val) =
    M.presheaf.map (face U a k).op (value π M U s (a.delete k)) :=
  ConcreteCategory.congr_hom (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface_comp_π π M U 0 k a) s.val

theorem cycle_pair (s : cycles π M U) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1) :
    M.presheaf.map (face U a 0).op (value π M U s (a.delete 0)) =
      M.presheaf.map (face U a 1).op (value π M U s (a.delete 1)) := by
  have h := congrArg (Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 1 j.1) a)
    (cofaces_eq π M U s)
  exact (coface_value π M U s a 0).symm.trans (h.trans (coface_value π M U s a 1))

theorem compatible_on (s : cycles π M U) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1)
    (V : X.Opens) (hV : V ≤ intersection U 1 a) :
    M.presheaf.map (homOfLE (hV.trans (leOfHom (face U a 0)))).op
      (value π M U s (a.delete 0)) =
    M.presheaf.map (homOfLE (hV.trans (leOfHom (face U a 1)))).op
      (value π M U s (a.delete 1)) := by
  have h := congrArg (M.presheaf.map (homOfLE hV).op) (cycle_pair π M U s a)
  rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply] at h
  exact h

end Construction.OrderedCechZeroCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq
