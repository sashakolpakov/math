import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries

/-! # Boundary Shuffle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.BoundaryShuffle

noncomputable section

section

/-! Literal regular triple sections representing the coboundary of
regular pair sections have zero class in the original sheaf H2. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

local instance regularTripleH2AddCommGroup :
    AddCommGroup (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 2) :=
  Cech.Add.cechClassAddCommGroup (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 2

def regularTripleCechCochain (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l)) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2 := fun a =>
  X.presheaf.map (homOfLE (le_inf (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1))
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 2))).op (w (a 0) (a 1) (a 2))

def RegularTripleBoundary (v : ∀ i j : I, Γ(X, U i ⊓ U j))
    (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l)) : Prop := ∀ i j l,
  X.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U l ≤ U j ⊓ U l from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (v j l) -
    X.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U l ≤ U i ⊓ U l from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (v i l) +
    X.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U l ≤ U i ⊓ U j from inf_le_left)).op (v i j) =
      w i j l

theorem regularPairCechCochain_delta (v : ∀ i j : I, Γ(X, U i ⊓ U j))
    (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l)) (hw : RegularTripleBoundary X U v w) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1 (RegularPair.Closed.regularPairCechCochain X U v) =
      regularTripleCechCochain X U w := by
  funext a
  rw [Cech.OneCocycleValues.abelianCechDelta_one]
  have hle : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ (U (a 0) ⊓ U (a 1)) ⊓ U (a 2) :=
    le_inf (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 2)
  have h := congrArg (fun s => X.presheaf.map (homOfLE hle).op s) (hw (a 0) (a 1) (a 2))
  rw [map_add, map_sub, RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp,
    RegularPair.Closed.regularSectionRestrict_comp] at h
  change (X.presheaf.map _ (X.presheaf.map _ (v (a 1) (a 2))) : Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) -
      (X.presheaf.map _ (X.presheaf.map _ (v (a 0) (a 2))) : Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) +
      (X.presheaf.map _ (X.presheaf.map _ (v (a 0) (a 1))) : Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) =
    X.presheaf.map (homOfLE hle).op (w (a 0) (a 1) (a 2))
  exact (congrArg₂ (fun b c : Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) => b + c)
    (congrArg₂ (fun b c : Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) => b - c)
      (RegularPair.Closed.regularSectionRestrict_comp X _ _ _) (RegularPair.Closed.regularSectionRestrict_comp X _ _ _))
    (RegularPair.Closed.regularSectionRestrict_comp X _ _ _)).trans h

theorem abelianCechDelta_squared {Y : TopCat.{0}} {J : Type} (V : J → Opens Y)
    (F : Y.Presheaf AddCommGrpCat.{0}) (n : ℕ) (b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F V n) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F V (n + 1) (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F V n b) = 0 := by
  apply (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F V (n + 2)).symm.injective
  rw [← DivisorClass.Chern.Cech.IntrinsicOperators.abelianCechCoordinates_symm_d, ← DivisorClass.Chern.Cech.IntrinsicOperators.abelianCechCoordinates_symm_d, map_zero]
  exact ConcreteCategory.congr_hom
    (((CategoryTheory.cechComplexFunctor V).obj F).d_comp_d n (n + 1) (n + 2))
    ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F V n).symm b)

theorem regularTripleCechCochain_closed (v : ∀ i j : I, Γ(X, U i ⊓ U j))
    (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l)) (hw : RegularTripleBoundary X U v w) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2 (regularTripleCechCochain X U w) = 0 := by
  rw [← regularPairCechCochain_delta X U v w hw]
  exact abelianCechDelta_squared U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 1 (RegularPair.Closed.regularPairCechCochain X U v)

theorem regularTripleCechClass_eq_zero (hU : iSup U = ⊤) (v : ∀ i j : I, Γ(X, U i ⊓ U j))
    (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l)) (hw : RegularTripleBoundary X U v w) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := X.toPresheafedSpace.carrier) U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1 (regularTripleCechCochain X U w)
      (regularTripleCechCochain_closed X U v w hw) =
        (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 2).obj
          (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf)) :=
  DivisorClass.Chern.Cech.SheafBoundaries.abelianCechSheafClass_eq_zero_of_boundary U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1
    (regularTripleCechCochain X U w) (regularTripleCechCochain_closed X U v w hw)
    (RegularPair.Closed.regularPairCechCochain X U v) (regularPairCechCochain_delta X U v w hw)

end

/-! Restricting a literal Cech boundary to four corners cancels its
diagonal term. This is the mixed shuffle identity needed on an actual
rectangular product cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

def regularPairSectionOn (v : ∀ i j, Γ(X, U i ⊓ U j))
    (a b : I) (W : X.Opens) (ha : W ≤ U a) (hb : W ≤ U b) : Γ(X, W) :=
  X.presheaf.map (homOfLE (le_inf ha hb)).op (v a b)

def regularTripleSectionOn (w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (a b c : I) (W : X.Opens) (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c) : Γ(X, W) :=
  X.presheaf.map (homOfLE (le_inf (le_inf ha hb) hc)).op (w a b c)

theorem regularTripleBoundary_restrict
    (v : ∀ i j, Γ(X, U i ⊓ U j)) (w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hw : RegularTripleBoundary X U v w)
    (a b c : I) (W : X.Opens) (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c) :
    regularTripleSectionOn X U w a b c W ha hb hc =
      regularPairSectionOn X U v b c W hb hc - regularPairSectionOn X U v a c W ha hc +
        regularPairSectionOn X U v a b W ha hb := by
  have h := congrArg (fun s => X.presheaf.map (homOfLE (le_inf (le_inf ha hb) hc)).op s) (hw a b c)
  rw [map_add, map_sub, RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp,
    RegularPair.Closed.regularSectionRestrict_comp] at h
  exact h.symm

theorem regularTripleBoundary_rectangleShuffle
    (v : ∀ i j, Γ(X, U i ⊓ U j)) (w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hw : RegularTripleBoundary X U v w)
    (a b c d : I) (W : X.Opens)
    (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c) (hd : W ≤ U d) :
    regularTripleSectionOn X U w a b c W ha hb hc -
        regularTripleSectionOn X U w a d c W ha hd hc =
      (regularPairSectionOn X U v b c W hb hc - regularPairSectionOn X U v a d W ha hd) -
        (regularPairSectionOn X U v d c W hd hc - regularPairSectionOn X U v a b W ha hb) := by
  rw [regularTripleBoundary_restrict X U v w hw a b c W ha hb hc,
    regularTripleBoundary_restrict X U v w hw a d c W ha hd hc]
  abel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.BoundaryShuffle
