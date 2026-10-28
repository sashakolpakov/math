import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelPrincipalFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryFractionLift

/-! # Model Principal Sheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelPrincipalSheaf

noncomputable section

/-! The actual additive single-sheaf fraction enters the native top
map through the same coefficient isomorphism and two universe lifts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem iso_value {A B C : AddCommGrpCat} (e e' : A ≅ B) (j : C ≅ B)
    (z : A) (y : C) (v : B) (he : e = e') (hz : v = e'.hom z) (hy : j.hom y = v) :
    e.hom z = j.hom y := by
  rw [he, hy, hz]

private theorem weighted_value {A B C : AddCommGrpCat} (e : A ≅ B) (f : C ⟶ B)
    (x y : A) (z : C) (a : ℤ) (hi : e.hom x = f (a • z)) (hz : f z = e.hom y) :
    x = a • y := by
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  rw [hi, map_zsmul, hz, map_zsmul]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (Z : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  (π : X ⟶ Z) (U : Z.left.Opens) (V : X.left.affineOpens)
  (hVU : V.val ≤ π.left ⁻¹ᵁ U)
  (g c : ℕ) [SmoothOfRelativeDimension g X.hom] (t : Fin g → Γ(Z.left,U))

abbrev parameters := ResidueFraction.localParameters p k n X Z π U V hVU g t
abbrev opens := ModelPrincipalFraction.opens p k n X V
abbrev family := ModelPrincipalFraction.family p k n X V g
  (parameters p k n X Z π U V hVU g t)
abbrev form := TopCover.form p k n X g
abbrev source := AffinePrincipal.Injective.Comparison.source
  (opens p k n X V) (family p k n X Z π U V hVU g t) (form p k n X g) c
abbrev localIso := PrincipalSheafValue.localCoordinates p k n X g c
  (opens p k n X V) (family p k n X Z π U V hVU g t)
abbrev nativeIso := ModelPrincipalFraction.localIso p k n X V g
  (parameters p k n X Z π U V hVU g t) c
abbrev input := PrincipalSheafValue.input p k n X g c
  (opens p k n X V) (family p k n X Z π U V hVU g t)

local instance tuple_preserves (d : ℕ) (z : Fin (d+1) → ULift (Fin g)) :
    PreservesLimit (Discrete.functor (family p k n X Z π U V hVU g t ∘ z)) (opens p k n X V) :=
  AffinePrincipal.Products.preserves X.left V.val V.property
    (family p k n X Z π U V hVU g t ∘ z)

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem coefficient_iso :
    PrincipalSheafValue.localCoefficientIso p k n X g
      (opens p k n X V) (family p k n X Z π U V hVU g t) =
    OrdinaryFractionLift.Ordinary.liftIso p k n X V g
      (parameters p k n X Z π U V hVU g t) g := rfl

omit [IsSeparated Y.hom] in
omit [IsProper X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem weighted (x : (source p k n X Z π U V hVU g c t).homology (g+c))
    (a : ℤ) (r : WittVector p k)
    (hx : (localIso p k n X Z π U V hVU g c t).hom x =
      a • OrdinaryFractionRestriction.Ordinary.targetClass p k n X Y f hp Z π U V hVU g t r) :
    input p k n X Z π U V hVU g c t (ULift.up.{2,1} (ULift.up.{1,0} x)) =
      a • ModelPrincipalFraction.input p k n X Y f hp V g
        (parameters p k n X Z π U V hVU g t) c r := by
  have hi := ConcreteCategory.congr_hom
    (PrincipalSheafValue.input_coordinates p k n X g c
      (opens p k n X V) (family p k n X Z π U V hVU g t))
    (ULift.up.{2,1} (ULift.up.{1,0} x))
  change (nativeIso p k n X Z π U V hVU g c t).hom
      (input p k n X Z π U V hVU g c t (ULift.up.{2,1} (ULift.up.{1,0} x))) =
    (PrincipalSheafValue.localCoefficientIso p k n X g
      (opens p k n X V) (family p k n X Z π U V hVU g t)).hom
      (ULift.up.{2,1} (ULift.up.{1,0} ((localIso p k n X Z π U V hVU g c t).hom x))) at hi
  rw [hx] at hi
  change _ = (PrincipalSheafValue.localCoefficientIso p k n X g
    (opens p k n X V) (family p k n X Z π U V hVU g t)).hom
    (a • ULift.up.{2,1} (ULift.up.{1,0}
    (OrdinaryFractionRestriction.Ordinary.targetClass p k n X Y f hp Z π U V hVU g t r))) at hi
  have hz := iso_value
    (PrincipalSheafValue.localCoefficientIso p k n X g
      (opens p k n X V) (family p k n X Z π U V hVU g t))
    (OrdinaryFractionLift.Ordinary.liftIso p k n X V g
      (parameters p k n X Z π U V hVU g t) g)
    (nativeIso p k n X Z π U V hVU g c t) _ _ _
    (coefficient_iso p k n X Z π U V hVU g t)
    (OrdinaryFractionLift.Ordinary.targetClass p k n X Y f hp V g Z π U hVU t r)
    (ModelPrincipalFraction.coordinates p k n X Y f hp V g
      (parameters p k n X Z π U V hVU g t) c r)
  exact weighted_value (nativeIso p k n X Z π U V hVU g c t) _ _ _ _ a hi hz

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelPrincipalSheaf
