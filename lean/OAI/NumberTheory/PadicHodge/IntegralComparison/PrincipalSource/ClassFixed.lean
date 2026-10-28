import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassCoordinates

/-! # Class Fixed -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassFixed.Coordinates

noncomputable section

/-! The explicit degree transport of the original principal class
preserves fixedness under the same coefficient endomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false

private theorem fixed_degree {R : Type*} [CommRing R] {F : ℕ → ModuleCat R}
    (a : ∀ q, F q ⟶ F q) {n m : ℕ} (h : n=m) (x : F n) (hx : a n x = x) :
    a m (eqToHom (congrArg F h) x) = eqToHom (congrArg F h) x := by
  subst m
  simpa only [eqToHom_refl, ModuleCat.id_apply] using hx

variable {Y X Z : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (N : Y.Modules)
  {m : ℕ} (t : Fin m → Γ(Z,U)) (c : ℕ)
  (α : ClassCoordinates.coefficient f i U hU N ⟶ ClassCoordinates.coefficient f i U hU N)
  (x : (ClassCoordinates.total f i U hU N t c).homology (c+m))

theorem cast_fixed
    (hx : (OpenRestriction.supportedFunctor U (ClassCoordinates.family U t) c (c+m)).map α x = x) :
    (OpenRestriction.supportedFunctor U (ClassCoordinates.family U t) c (m+c)).map α
      (ClassCoordinates.cast f i U hU N t c x) = ClassCoordinates.cast f i U hU N t c x :=
  fixed_degree (F := fun q => (ClassCoordinates.total f i U hU N t c).homology q)
    (fun q => (OpenRestriction.supportedFunctor U (ClassCoordinates.family U t) c q).map α)
    (Nat.add_comm c m) x hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassFixed.Coordinates
