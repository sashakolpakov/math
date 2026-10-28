import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalScalarEquation

/-! # Scalar Equation Family Points -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarEquationFamilyPoints

noncomputable section

/-! Over a base scheme, a global scalar equation represents exactly
the morphisms on which that equation holds in global functions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {S : Scheme.{u}} (M : Over S) (a : Γ(M.left, ⊤))

def scalarEqOneFamily : Over S := Over.mk ((GlobalScalarEquation.Construction.scalarEqOneScheme M.left a).hom ≫ M.hom)

def scalarEqOneFamilyInclusion : scalarEqOneFamily M a ⟶ M :=
  Over.homMk (GlobalScalarEquation.Construction.scalarEqOneScheme M.left a).hom rfl

instance scalarEqOneFamilyInclusion_isClosedImmersion :
    IsClosedImmersion (scalarEqOneFamilyInclusion M a).left :=
  inferInstanceAs (IsClosedImmersion (GlobalScalarEquation.Construction.scalarEqOneScheme M.left a).hom)

def scalarEqOneFamilyLift (T : Over S) (p : T ⟶ M) (hp : p.left.appTop a = 1) :
    T ⟶ scalarEqOneFamily M a := by
  let q := Classical.choice ((GlobalScalarEquation.Construction.scalarEqOneScheme_hasLift_iff a p.left).mpr hp)
  refine Over.homMk q.left ?_
  change q.left ≫ ((GlobalScalarEquation.Construction.scalarEqOneScheme M.left a).hom ≫ M.hom) = T.hom
  rw [← Category.assoc, q.w]
  exact p.w

theorem scalarEqOneFamilyLift_fac (T : Over S) (p : T ⟶ M) (hp : p.left.appTop a = 1) :
    scalarEqOneFamilyLift M a T p hp ≫ scalarEqOneFamilyInclusion M a = p := by
  apply Over.OverMorphism.ext
  exact (Classical.choice ((GlobalScalarEquation.Construction.scalarEqOneScheme_hasLift_iff a p.left).mpr hp)).w

def scalarEqOneFamilyPointEquiv (T : Over S) :
    (T ⟶ scalarEqOneFamily M a) ≃ { p : T ⟶ M // p.left.appTop a = 1 } where
  toFun q := ⟨q ≫ scalarEqOneFamilyInclusion M a,
    (GlobalScalarEquation.Construction.scalarEqOneScheme_hasLift_iff a (q.left ≫ (GlobalScalarEquation.Construction.scalarEqOneScheme M.left a).hom)).mp
      ⟨Over.homMk q.left rfl⟩⟩
  invFun p := scalarEqOneFamilyLift M a T p.val p.property
  left_inv q := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (GlobalScalarEquation.Construction.scalarEqOneScheme M.left a).hom).mp
    exact congrArg Over.Hom.left (scalarEqOneFamilyLift_fac M a T
      (q ≫ scalarEqOneFamilyInclusion M a)
        ((GlobalScalarEquation.Construction.scalarEqOneScheme_hasLift_iff a (q.left ≫ (GlobalScalarEquation.Construction.scalarEqOneScheme M.left a).hom)).mp
          ⟨Over.homMk q.left rfl⟩))
  right_inv p := Subtype.ext (scalarEqOneFamilyLift_fac M a T p.val p.property)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarEquationFamilyPoints
