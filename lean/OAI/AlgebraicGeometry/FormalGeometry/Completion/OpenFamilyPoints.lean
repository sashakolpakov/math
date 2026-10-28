import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

/-! # Open Family Points -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenFamilyPoints

noncomputable section

/-! Morphisms to an open subscheme over a base are exactly the morphisms
to its ambient scheme whose images lie in that open. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {S : Scheme.{u}} (M : Over S) (U : M.left.Opens)

def openFamily : Over S := Over.mk (U.ι ≫ M.hom)

def openFamilyInclusion : openFamily M U ⟶ M := Over.homMk U.ι rfl

def openFamilyLift (T : Over S) (p : T ⟶ M) (hp : ∀ y : T.left, p.left y ∈ U) :
    T ⟶ openFamily M U := by
  have hr : Set.range p.left ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨p.left y, hp y⟩, rfl⟩
  refine Over.homMk (IsOpenImmersion.lift U.ι p.left hr) ?_
  change IsOpenImmersion.lift U.ι p.left hr ≫ (U.ι ≫ M.hom) = T.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact p.w

theorem openFamilyLift_fac (T : Over S) (p : T ⟶ M) (hp : ∀ y : T.left, p.left y ∈ U) :
    openFamilyLift M U T p hp ≫ openFamilyInclusion M U = p := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac U.ι p.left _

def openFamilyPointEquiv (T : Over S) :
    (T ⟶ openFamily M U) ≃ { p : T ⟶ M // ∀ y : T.left, p.left y ∈ U } where
  toFun a := ⟨a ≫ openFamilyInclusion M U, fun y => (a.left y).property⟩
  invFun p := openFamilyLift M U T p.val p.property
  left_inv a := by
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    exact IsOpenImmersion.lift_fac U.ι (a.left ≫ U.ι) _
  right_inv p := Subtype.ext (openFamilyLift_fac M U T p.val p.property)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenFamilyPoints
