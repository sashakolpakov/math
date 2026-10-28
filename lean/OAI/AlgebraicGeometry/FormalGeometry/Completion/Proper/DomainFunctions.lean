import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ConnectedFunctions

/-! # Domain Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.DomainFunctions.Construction

noncomputable section

/-!
# Completion: proper global function domains are finite fields

Only the domain property of the actual global section ring is needed;
the whole scheme need not already have been proved integral.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsDomain Γ(X, ⊤)]

include f

/-- A proper scheme whose actual global sections form a domain has a global function field. -/
theorem proper_globalFunctionDomain_isField : IsField Γ(X, ⊤) := by
  have := ConnectedFunctions.Construction.proper_globalFunctions_krullDimLE_zero K f
  exact Ring.KrullDimLE.isField_of_isDomain

/-- That actual global function field is finite over the structural base field. -/
theorem proper_globalFunctionDomain_finite : f.appTop.hom.Finite := by
  have : Surjective X.toSpecΓ := Affinization.Construction.proper_toSpecΓ_surjective f
  let z : Spec Γ(X, ⊤) := Nonempty.some inferInstance
  obtain ⟨x, _⟩ := X.toSpecΓ.surjective z
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  let := (proper_globalFunctionDomain_isField K f).toField
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply RingHom.finite_of_algHom_finiteType_of_isJacobsonRing (A := Γ(X, U))
    (g := (X.presheaf.map (homOfLE le_top).op).hom)
  exact f.finiteType_appLE (isAffineOpen_top _) hU (by simp)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.DomainFunctions.Construction
