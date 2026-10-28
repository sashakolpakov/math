import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.OneCocycleValues
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClasses
import Mathlib.AlgebraicGeometry.Restrict
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add

/-! # Closed -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed

noncomputable section

section

/-! Original regular sections on pair intersections define the
native abelian Cech cocycle when they satisfy the triple equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0})

theorem regularSectionRestrict_comp {U V W : X.Opens} (h : V ≤ U) (j : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE j).op (X.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE (j.trans h)).op s := by
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

variable {I : Type} (U : I → X.Opens) (v : ∀ i j : I, Γ(X, U i ⊓ U j))

def regularPairCechCochain : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (X := X.toPresheafedSpace.carrier)
    (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1 := fun a =>
  X.presheaf.map (homOfLE (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1))).op (v (a 0) (a 1))

def RegularPairCocycle : Prop := ∀ i j l : I,
  X.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U l ≤ U i ⊓ U j from inf_le_left)).op (v i j) +
    X.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U l ≤ U j ⊓ U l from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (v j l) =
    X.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U l ≤ U i ⊓ U l from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (v i l)

theorem regularPairCechCochain_closed (hv : RegularPairCocycle X U v) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1
      (regularPairCechCochain X U v) = 0 := by
  apply Cech.OneCocycleValues.abelianCech_one_closed_of_transition (X := X.toPresheafedSpace.carrier)
  intro a
  have hle : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ (U (a 0) ⊓ U (a 1)) ⊓ U (a 2) :=
    le_inf (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 2)
  have h := congrArg (fun s => X.presheaf.map (homOfLE hle).op s) (hv (a 0) (a 1) (a 2))
  rw [map_add, regularSectionRestrict_comp, regularSectionRestrict_comp, regularSectionRestrict_comp] at h
  change X.presheaf.map _ (X.presheaf.map _ (v (a 1) (a 2))) +
      X.presheaf.map _ (X.presheaf.map _ (v (a 0) (a 1))) =
    X.presheaf.map _ (X.presheaf.map _ (v (a 0) (a 2)))
  exact (congrArg₂ (· + ·) (regularSectionRestrict_comp X _ _ _) (regularSectionRestrict_comp X _ _ _)).trans
    ((add_comm _ _).trans (h.trans (regularSectionRestrict_comp X _ _ _).symm))

end

section

/-! An actual regular pair cocycle defines a native degree-one sheaf
class. A zero class supplies a literal primitive on the original cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens) (hU : iSup U = ⊤)
    (v : ∀ i j : I, Γ(X, U i ⊓ U j)) (hv : RegularPairCocycle X U v)

def regularPairSheafClass : CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 1 :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 0 (regularPairCechCochain X U v)
    (regularPairCechCochain_closed X U v hv)

theorem regularPairSheafClass_zero_boundary
    (hz : regularPairSheafClass X U hU v hv =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 1).obj
        (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf))) :
    ∃ c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 0,
      DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 0 c = regularPairCechCochain X U v :=
  Cech.Add.cech_one_boundary_of_sheaf_class_zero U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU
    (regularPairCechCochain X U v) (regularPairCechCochain_closed X U v hv) hz

end

/-! A native Cech boundary for regular pair sections gives actual
regular primitives on the original opens, with the transition sign. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens) (v : ∀ i j : I, Γ(X, U i ⊓ U j))

def RegularPairPrimitive (s : ∀ i : I, Γ(X, U i)) : Prop := ∀ i j : I,
  v i j = X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (s i) -
    X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (s j)

theorem regularPairPrimitive_of_cech_boundary
    (c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 0)
    (hc : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 0 c = regularPairCechCochain X U v) :
    ∃ s : ∀ i : I, Γ(X, U i), RegularPairPrimitive X U v s := by
  obtain ⟨s, hs⟩ := Cech.Add.cech_zero_eq_localSections U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) c
  let r : ∀ i : I, Γ(X, U i) := fun i => s i
  refine ⟨fun i => -r i, fun i j => ?_⟩
  let a : Fin 2 → I := Fin.cases i (fun _ => j)
  have h0 : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ U i := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0
  have h1 : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ U j := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1
  have hp : U i ⊓ U j ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a := by
    intro x hx
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U a x).mpr
    intro t
    exact Fin.cases hx.1 (fun _ => hx.2) t
  have hd : X.presheaf.map (homOfLE h1).op (r j) - X.presheaf.map (homOfLE h0).op (r i) =
      X.presheaf.map (homOfLE (le_inf h0 h1)).op (v i j) := by
    have h := congrFun hc a
    rw [← hs, DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta] at h
    exact h
  have h := congrArg (fun w => X.presheaf.map (homOfLE hp).op w) hd
  rw [map_sub, regularSectionRestrict_comp, regularSectionRestrict_comp, regularSectionRestrict_comp] at h
  have hr : X.presheaf.map (homOfLE (hp.trans (le_inf h0 h1))).op (v i j) = v i j := by
    change X.presheaf.map (𝟙 (.op (U i ⊓ U j))) (v i j) = v i j
    exact X.presheaf.map_id_apply _ _
  rw [hr] at h
  change v i j = X.presheaf.map (homOfLE inf_le_left).op (-r i) -
    X.presheaf.map (homOfLE inf_le_right).op (-r j)
  rw [map_neg, map_neg]
  exact h.symm.trans (by abel)

theorem regularPairPrimitive_of_sheafClass_zero (hU : iSup U = ⊤) (hv : RegularPairCocycle X U v)
    (hz : regularPairSheafClass X U hU v hv =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 1).obj
        (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf))) :
    ∃ s : ∀ i : I, Γ(X, U i), RegularPairPrimitive X U v s := by
  obtain ⟨c, hc⟩ := regularPairSheafClass_zero_boundary X U hU v hv hz
  exact regularPairPrimitive_of_cech_boundary X U v c hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
