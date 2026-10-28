import Mathlib.AlgebraicGeometry.Restrict

/-! # Section Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.SectionTransport

noncomputable section

/-! Canonical transport along equal algebraic opens preserves their
actual rings of sections and commutes with restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def regularSectionTransport {X : Scheme.{0}} {U V : X.Opens} (h : U = V) : Γ(X, U) ≃+* Γ(X, V) := by
  subst V
  exact RingEquiv.refl _

theorem regularSectionTransport_restrict {X : Scheme.{0}} {U V U' V' : X.Opens}
    (hU : U = U') (hV : V = V') (h : V ≤ U) (h' : V' ≤ U') (s : Γ(X, U)) :
    regularSectionTransport hV (X.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h').op (regularSectionTransport hU s) := by
  subst U'
  subst V'
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.SectionTransport
