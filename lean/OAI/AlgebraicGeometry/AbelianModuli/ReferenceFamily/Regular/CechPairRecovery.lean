import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.BoundaryShuffle

/-! # Cech Pair Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechPairRecovery

noncomputable section

/-! Actual tuple-indexed regular Cech cochains recover literal
sections on pair and triple intersections. Thus a native degree-two
boundary supplies a regular pair primitive without changing the cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

theorem regularPairIntersection_le (i j : I) :
    U i ⊓ U j ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Fin.cases i (fun _ : Fin 1 => j)) := by
  intro x hx
  apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U _ x).mpr
  intro t
  exact Fin.cases hx.1 (fun _ => hx.2) t

def regularPairOfCech
    (c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1)
    (i j : I) : Γ(X, U i ⊓ U j) := by
  let a : Fin 2 → I := Fin.cases i (fun _ : Fin 1 => j)
  have v : Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) := c a
  exact X.presheaf.map (homOfLE (regularPairIntersection_le X U i j)).op v

theorem regularPairOfCech_recovery
    (c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1) :
    RegularPair.Closed.regularPairCechCochain X U (regularPairOfCech X U c) = c := by
  funext a
  have hh (i j : I) :
      RegularPair.Closed.regularPairCechCochain X U (regularPairOfCech X U c) (Fin.cases i (fun _ : Fin 1 => j)) =
        c (Fin.cases i (fun _ : Fin 1 => j)) := by
    unfold RegularPair.Closed.regularPairCechCochain regularPairOfCech
    dsimp only
    erw [RegularPair.Closed.regularSectionRestrict_comp]
    change X.presheaf.map (𝟙 _) (c _) = c _
    exact X.presheaf.map_id_apply _ _
  have he : Fin.cases (a 0) (fun _ : Fin 1 => a 1) = a := by
    funext t
    fin_cases t <;> rfl
  exact he ▸ hh (a 0) (a 1)

theorem regularTripleCechCochain_injective :
    Function.Injective (BoundaryShuffle.regularTripleCechCochain X U) := by
  intro w z h
  funext i j l
  let a : Fin 3 → I := Fin.cases i (Fin.cases j (fun _ => l))
  have hW : (U i ⊓ U j) ⊓ U l ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a := by
    intro x hx
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U a x).mpr
    intro t
    exact Fin.cases hx.1.1 (Fin.cases hx.1.2 (fun _ => hx.2)) t
  have he := congrArg (fun s => X.presheaf.map (homOfLE hW).op s) (congrFun h a)
  change X.presheaf.map (homOfLE hW).op
      (X.presheaf.map (homOfLE (le_inf (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 2))).op (w i j l)) =
    X.presheaf.map (homOfLE hW).op
      (X.presheaf.map (homOfLE (le_inf (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 2))).op (z i j l)) at he
  rw [RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp] at he
  change X.presheaf.map (𝟙 _) (w i j l) = X.presheaf.map (𝟙 _) (z i j l) at he
  erw [X.presheaf.map_id_apply, X.presheaf.map_id_apply] at he
  exact he

def regularPairBoundaryTriple (v : ∀ i j, Γ(X, U i ⊓ U j))
    (i j l : I) : Γ(X, (U i ⊓ U j) ⊓ U l) :=
  X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (v j l) -
    X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (v i l) +
    X.presheaf.map (homOfLE inf_le_left).op (v i j)

theorem regularTriplePrimitive_of_cech_boundary
    (w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1)
    (hc : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1 c = BoundaryShuffle.regularTripleCechCochain X U w) :
    ∃ v : ∀ i j, Γ(X, U i ⊓ U j), BoundaryShuffle.RegularTripleBoundary X U v w := by
  let v := regularPairOfCech X U c
  have h := (BoundaryShuffle.regularPairCechCochain_delta X U v (regularPairBoundaryTriple X U v)
    (fun _ _ _ => rfl)).symm.trans
      ((congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1)
        (regularPairOfCech_recovery X U c)).trans hc)
  have he := regularTripleCechCochain_injective X U h
  exact ⟨v, fun i j l => congrFun (congrFun (congrFun he i) j) l⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechPairRecovery
