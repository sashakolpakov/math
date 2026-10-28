import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ConnectedFunctions
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Connected Field -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ConnectedField.Construction

noncomputable section

/-!
# Completion: the field of functions on a connected reduced proper fiber

The global field is finite over the base field. Over an algebraically
closed field, the actual structural map is an isomorphism.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [ConnectedSpace X] [IsReduced X]

/-- The global functions of a connected reduced proper fiber form a finite field extension. -/
theorem proper_connected_reduced_globalFunctions_finite : f.appTop.hom.Finite := by
  have x : X := Nonempty.some inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  let := (ConnectedFunctions.Construction.proper_connected_reduced_globalFunctions_isField K f).toField
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply RingHom.finite_of_algHom_finiteType_of_isJacobsonRing (A := Γ(X, U))
    (g := (X.presheaf.map (homOfLE le_top).op).hom)
  exact f.finiteType_appLE (isAffineOpen_top _) hU (by simp)

/-- A connected reduced proper geometric fiber has only constant global functions. -/
theorem proper_connected_reduced_appTop_isIso [IsAlgClosed K] : IsIso f.appTop := by
  let := (ConnectedFunctions.Construction.proper_connected_reduced_globalFunctions_isField K f).toField
  let F : CommRingCat.of K ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  have : IsIso F := (ConcreteCategory.isIso_iff_bijective F).mpr
    (IsAlgClosed.ringHom_bijective_of_isIntegral F.hom hF)
  exact (isIso_comp_left_iff (Scheme.ΓSpecIso _).inv f.appTop).mp this

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ConnectedField.Construction
