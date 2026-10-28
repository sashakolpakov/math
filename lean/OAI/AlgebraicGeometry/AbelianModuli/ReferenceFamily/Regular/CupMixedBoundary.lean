import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupClassAddition

/-! # Cup Mixed Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupMixedBoundary

noncomputable section

section

/-! Literal regular boundary witnesses can be added, subtracted and
summed. Equal original H1 classes give an actual boundary for the
difference of their cups on the same cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped BigOperators

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

theorem regularTripleBoundary_add
    (p q : ∀ i j, Γ(X, U i ⊓ U j))
    (v w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hp : BoundaryShuffle.RegularTripleBoundary X U p v) (hq : BoundaryShuffle.RegularTripleBoundary X U q w) :
    BoundaryShuffle.RegularTripleBoundary X U (fun i j => p i j + q i j)
      (fun i j l => v i j l + w i j l) := by
  intro i j l
  simp only [map_add]
  have h := congrArg₂ (· + ·) (hp i j l) (hq i j l)
  convert h using 1
  abel

theorem regularTripleBoundary_sub
    (p q : ∀ i j, Γ(X, U i ⊓ U j))
    (v w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hp : BoundaryShuffle.RegularTripleBoundary X U p v) (hq : BoundaryShuffle.RegularTripleBoundary X U q w) :
    BoundaryShuffle.RegularTripleBoundary X U (fun i j => p i j - q i j)
      (fun i j l => v i j l - w i j l) := by
  intro i j l
  simp only [map_sub]
  have h := congrArg₂ (· - ·) (hp i j l) (hq i j l)
  convert h using 1
  abel

theorem regularTripleBoundary_sum {B : Type} (t : Finset B)
    (p : B → ∀ i j, Γ(X, U i ⊓ U j))
    (v : B → ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hp : ∀ a ∈ t, BoundaryShuffle.RegularTripleBoundary X U (p a) (v a)) :
    BoundaryShuffle.RegularTripleBoundary X U (fun i j => ∑ a ∈ t, p a i j)
      (fun i j l => ∑ a ∈ t, v a i j l) := by
  intro i j l
  simp only [map_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a ha => hp a ha i j l)

theorem regularPairCup_differenceBoundary (hU : iSup U = ⊤)
    (v v' w w' : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hv' : RegularPair.Closed.RegularPairCocycle X U v')
    (hw : RegularPair.Closed.RegularPairCocycle X U w) (hw' : RegularPair.Closed.RegularPairCocycle X U w')
    (hvv' : RegularPair.Closed.regularPairSheafClass X U hU v hv = RegularPair.Closed.regularPairSheafClass X U hU v' hv')
    (hww' : RegularPair.Closed.regularPairSheafClass X U hU w hw = RegularPair.Closed.regularPairSheafClass X U hU w' hw') :
    ∃ p : ∀ i j, Γ(X, U i ⊓ U j), BoundaryShuffle.RegularTripleBoundary X U p
      (fun i j l => RegularPair.CupSymmetry.regularPairCupTriple X U v w i j l - RegularPair.CupSymmetry.regularPairCupTriple X U v' w' i j l) := by
  obtain ⟨s, hs⟩ := CupClassAddition.regularPairPrimitive_of_sheafClass_eq X U hU v v' hv hv' hvv'
  obtain ⟨t, ht⟩ := CupClassAddition.regularPairPrimitive_of_sheafClass_eq X U hU w w' hw hw' hww'
  have hl := RegularPair.CupPrimitives.regularPairCup_leftPrimitive X U (fun i j => v i j - v' i j) w s hs hw
  have hr := RegularPair.CupPrimitives.regularPairCup_rightPrimitive X U v' (fun i j => w i j - w' i j) t hv' ht
  refine ⟨fun i j => -RegularPair.CupPrimitives.regularCupFrontPair X U s w i j + RegularPair.CupPrimitives.regularCupBackPair X U v' t i j, ?_⟩
  have h := regularTripleBoundary_add X U _ _ _ _ hl hr
  intro i j l
  refine (h i j l).trans ?_
  dsimp only [RegularPair.CupSymmetry.regularPairCupTriple]
  rw [map_sub, map_sub]
  ring

end

/-! On a common cover, primitive degree-one pullback classes and
the three actual diagonal cup boundaries force a literal mixed cup
boundary. This step uses only the original regular sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

local instance mixedBoundaryH1Group :
    AddCommGroup (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 1) :=
  Cech.Add.cechClassAddCommGroup (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 1

theorem regularCupMixedBoundary_of_three_boundaries
    (hU : iSup U = ⊤) {B : Type} [Fintype B]
    (v₀ v₁ v₂ w₀ w₁ w₂ : B → ∀ i j, Γ(X, U i ⊓ U j))
    (hv₀ : ∀ a, RegularPair.Closed.RegularPairCocycle X U (v₀ a))
    (hv₁ : ∀ a, RegularPair.Closed.RegularPairCocycle X U (v₁ a))
    (hv₂ : ∀ a, RegularPair.Closed.RegularPairCocycle X U (v₂ a))
    (hw₀ : ∀ a, RegularPair.Closed.RegularPairCocycle X U (w₀ a))
    (hw₁ : ∀ a, RegularPair.Closed.RegularPairCocycle X U (w₁ a))
    (hw₂ : ∀ a, RegularPair.Closed.RegularPairCocycle X U (w₂ a))
    (hv : ∀ a, RegularPair.Closed.regularPairSheafClass X U hU (v₀ a) (hv₀ a) =
      RegularPair.Closed.regularPairSheafClass X U hU (v₁ a) (hv₁ a) +
        RegularPair.Closed.regularPairSheafClass X U hU (v₂ a) (hv₂ a))
    (hw : ∀ a, RegularPair.Closed.regularPairSheafClass X U hU (w₀ a) (hw₀ a) =
      RegularPair.Closed.regularPairSheafClass X U hU (w₁ a) (hw₁ a) +
        RegularPair.Closed.regularPairSheafClass X U hU (w₂ a) (hw₂ a))
    (p₀ p₁ p₂ : ∀ i j, Γ(X, U i ⊓ U j))
    (hp₀ : BoundaryShuffle.RegularTripleBoundary X U p₀
      (fun i j l => ∑ a, RegularPair.CupSymmetry.regularPairCupTriple X U (v₀ a) (w₀ a) i j l))
    (hp₁ : BoundaryShuffle.RegularTripleBoundary X U p₁
      (fun i j l => ∑ a, RegularPair.CupSymmetry.regularPairCupTriple X U (v₁ a) (w₁ a) i j l))
    (hp₂ : BoundaryShuffle.RegularTripleBoundary X U p₂
      (fun i j l => ∑ a, RegularPair.CupSymmetry.regularPairCupTriple X U (v₂ a) (w₂ a) i j l)) :
    ∃ p : ∀ i j, Γ(X, U i ⊓ U j), BoundaryShuffle.RegularTripleBoundary X U p
      (fun i j l => ∑ a, (RegularPair.CupSymmetry.regularPairCupTriple X U (v₁ a) (w₂ a) i j l +
        RegularPair.CupSymmetry.regularPairCupTriple X U (v₂ a) (w₁ a) i j l)) := by
  classical
  have hdiff (a : B) : ∃ q : ∀ i j, Γ(X, U i ⊓ U j), BoundaryShuffle.RegularTripleBoundary X U q
      (fun i j l => RegularPair.CupSymmetry.regularPairCupTriple X U (v₀ a) (w₀ a) i j l -
        RegularPair.CupSymmetry.regularPairCupTriple X U (fun i j => v₁ a i j + v₂ a i j)
          (fun i j => w₁ a i j + w₂ a i j) i j l) := by
    apply regularPairCup_differenceBoundary X U hU (v₀ a) _ (w₀ a) _
      (hv₀ a) (RegularPair.ClassAddition.regularPairCocycle_add X U (v₁ a) (v₂ a) (hv₁ a) (hv₂ a))
      (hw₀ a) (RegularPair.ClassAddition.regularPairCocycle_add X U (w₁ a) (w₂ a) (hw₁ a) (hw₂ a))
    · exact (hv a).trans
        (RegularPair.ClassAddition.regularPairSheafClass_add X U (v₁ a) (v₂ a) hU (hv₁ a) (hv₂ a)).symm
    · exact (hw a).trans
        (RegularPair.ClassAddition.regularPairSheafClass_add X U (w₁ a) (w₂ a) hU (hw₁ a) (hw₂ a)).symm
  choose q hq using hdiff
  have hs := regularTripleBoundary_sum X U Finset.univ q _ (fun a _ => hq a)
  have h₀ := regularTripleBoundary_sub X U _ _ _ _ hp₀ hs
  have h₁ := regularTripleBoundary_sub X U _ _ _ _ h₀ hp₁
  have h₂ := regularTripleBoundary_sub X U _ _ _ _ h₁ hp₂
  refine ⟨fun i j => ((p₀ i j - ∑ a, q a i j) - p₁ i j) - p₂ i j, ?_⟩
  intro i j l
  refine (h₂ i j l).trans ?_
  dsimp only
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [RegularPair.CupSymmetry.regularPairCupTriple]
  rw [map_add, map_add]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupMixedBoundary
