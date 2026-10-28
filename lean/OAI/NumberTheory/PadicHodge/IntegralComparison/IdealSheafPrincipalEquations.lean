import OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalKoszulPurity
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Flat.Localization

/-! # Ideal Sheaf Principal Equations -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations

noncomputable section

/-! The actual ideal sheaf and its regular equations localize on a
principal open. The quotient algebra uses the literal restriction map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) (hU : IsAffineOpen U)
  (r : Γ(X, U))

abbrev principalIdeal := I.ideal ⟨X.basicOpen r, hU.basicOpen r⟩

theorem ideal_map :
    (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) Γ(X, X.basicOpen r)) = principalIdeal I U hU r :=
  I.map_ideal_basicOpen ⟨U, hU⟩ r

def quotientMap :
    (Γ(X, U) ⧸ I.ideal ⟨U, hU⟩) →+* (Γ(X, X.basicOpen r) ⧸ principalIdeal I U hU r) :=
  Ideal.quotientMap (principalIdeal I U hU r)
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    (I.ideal_le_comap_ideal (U := ⟨X.basicOpen r, hU.basicOpen r⟩) (V := ⟨U, hU⟩)
      (X.basicOpen_le r))

abbrev quotientAlgebra :
    Algebra (Γ(X, U) ⧸ I.ideal ⟨U, hU⟩) (Γ(X, X.basicOpen r) ⧸ principalIdeal I U hU r) :=
  (IdealSheafPrincipalEquations.quotientMap I U hU r).toAlgebra

theorem quotient_isLocalization :
    letI := quotientAlgebra I U hU r
    IsLocalization.Away (Ideal.Quotient.mk (I.ideal ⟨U, hU⟩) r)
      (Γ(X, X.basicOpen r) ⧸ principalIdeal I U hU r) :=
  I.isLocalization_away (U := ⟨X.basicOpen r, hU.basicOpen r⟩) (V := ⟨U, hU⟩)
    (X.basicOpen_le r) r (Subtype.ext rfl)

variable {c : ℕ} (s : Fin c → Γ(X, U))

def sequence : Fin c → Γ(X, X.basicOpen r) :=
  fun j => X.presheaf.map (homOfLE (X.basicOpen_le r)).op (s j)

theorem generates
    (hs : Koszul.OrientedTopCohomology.ideal Γ(X, U) s = I.ideal ⟨U, hU⟩) :
    Koszul.OrientedTopCohomology.ideal Γ(X, X.basicOpen r) (sequence U r s) =
      principalIdeal I U hU r := by
  rw [← ideal_map, ← hs]
  change Ideal.span (Set.range (sequence U r s)) =
    (Ideal.span (Set.range s)).map (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

include hU in
theorem weaklyRegular (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s)) :
    RingTheory.Sequence.IsWeaklyRegular Γ(X, X.basicOpen r) (List.ofFn (sequence U r s)) := by
  let : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, X.basicOpen r) :=
    IsLocalization.flat Γ(X, X.basicOpen r) (Submonoid.powers r)
  change RingTheory.Sequence.IsWeaklyRegular Γ(X, X.basicOpen r)
    (List.ofFn (fun j => algebraMap Γ(X, U) Γ(X, X.basicOpen r) (s j)))
  simpa only [List.map_ofFn, Function.comp_def] using
    (hreg.of_flat (S := Γ(X, X.basicOpen r)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations
