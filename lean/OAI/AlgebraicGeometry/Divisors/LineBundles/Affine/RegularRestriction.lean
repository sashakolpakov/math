import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Regular Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.RegularRestriction.BundleCycles

noncomputable section

/-! A regular section on an affine open stays regular on
every smaller affine open, by the genuine flat restriction map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineRestriction_flat {X : Scheme.{0}} (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    (X.presheaf.map (homOfLE h).op).hom.Flat := by
  have H := Scheme.Hom.flat_appLE (𝟙 X) U.2 V.2 h
  exact H

theorem affineRestriction_regular {X : Scheme.{0}} (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (t : Γ(X, U.1)) (ht : IsRegular t) : IsRegular (X.presheaf.map (homOfLE h).op t) := by
  let φ := (X.presheaf.map (homOfLE h).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := φ.toAlgebra
  let : Module.Flat Γ(X, U.1) Γ(X, V.1) := affineRestriction_flat U V h
  have hl : IsLeftRegular (φ t) := Module.Flat.isSMulRegular_of_isRegular ht
  exact ⟨hl, fun a b H => hl ((mul_comm _ _).trans (H.trans (mul_comm _ _)))⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.RegularRestriction.BundleCycles
