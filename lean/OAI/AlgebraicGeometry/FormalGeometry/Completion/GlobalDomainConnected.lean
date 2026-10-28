import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.Connected.Clopen

/-! # Global Domain Connected -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalDomainConnected.Construction

noncomputable section

/-!
# Completion: a scheme with a global function domain is connected

A separation into two nonempty open-and-closed pieces would split global
functions as a product of two nontrivial rings, contradicting the domain
property. This is applied to actual flat base changes of global sections.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Nontrivial global functions force the actual scheme to be nonempty. -/
theorem scheme_nonempty_of_nontrivial_globalFunctions (X : Scheme.{u})
    [Nontrivial Γ(X, ⊤)] : Nonempty X := by
  by_contra hn
  have : IsEmpty X := not_nonempty_iff.mp hn
  have he : ((⊤ : X.Opens) : Set X) = ∅ := Set.eq_empty_of_isEmpty _
  have : Subsingleton Γ(X, ⊤) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (TopologicalSpace.Opens.ext he))
  exact zero_ne_one (Subsingleton.elim (0 : Γ(X, ⊤)) 1)

/-- The actual global function domain rules out a disconnected decomposition of the scheme. -/
theorem scheme_connected_of_globalFunctionDomain (X : Scheme.{u})
    [IsDomain Γ(X, ⊤)] : ConnectedSpace X := by
  rw [connectedSpace_iff_clopen]
  refine ⟨scheme_nonempty_of_nontrivial_globalFunctions X, ?_⟩
  intro s hs
  by_cases hse : s = ∅
  · exact Or.inl hse
  by_cases hsu : s = Set.univ
  · exact Or.inr hsu
  exfalso
  let U : X.Opens := ⟨s, hs.isOpen⟩
  let V : X.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  have : Nonempty U := (Set.nonempty_iff_ne_empty.mpr hse).to_subtype
  have : Nonempty V := by
    have hn : sᶜ ≠ ∅ := by
      intro he
      apply hsu
      simpa using congrArg (fun t : Set X => tᶜ) he
    exact (Set.nonempty_iff_ne_empty.mpr hn).to_subtype
  have hu : U ⊔ V = ⊤ := by ext; simp [U, V]
  have hd : U ⊓ V = ⊥ := by ext; simp [U, V]
  let e : Γ(X, ⊤) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
    X.presheaf.mapIso (eqToIso hu).op ≪≫
      (X.sheaf.isProductOfDisjoint U V hd).conePointUniqueUpToIso
        (CommRingCat.prodFanIsLimit Γ(X, U) Γ(X, V))
  have : IsDomain (Γ(X, U) × Γ(X, V)) := e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have hm : ((1, 0) : Γ(X, U) × Γ(X, V)) * (0, 1) = 0 := by simp
  rcases mul_eq_zero.mp hm with h | h
  · exact one_ne_zero (congrArg Prod.fst h)
  · exact one_ne_zero (congrArg Prod.snd h)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalDomainConnected.Construction
