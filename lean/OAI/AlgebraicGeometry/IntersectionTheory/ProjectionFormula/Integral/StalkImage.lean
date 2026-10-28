import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

/-! # Stalk Image -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.StalkImage

noncomputable section

/-! The prime kernel of a stalk map from an integral source maps to the
actual image of its generic point. This applies to nested singular supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme} [IsIntegral Y] (i : Y ⟶ X) (y : Y) (x : X) (h : i y = x)

def map : X.presheaf.stalk x ⟶ Y.presheaf.stalk y :=
  eqToHom (congrArg (fun t => X.presheaf.stalk t) h.symm) ≫ i.stalkMap y

def prime : PrimeSpectrum (X.presheaf.stalk x) :=
  ⟨RingHom.ker (StalkImage.map i y x h).hom, Ideal.isPrime_bot.comap (StalkImage.map i y x h).hom⟩

theorem image : X.fromSpecStalk x (prime i y x h) = i (genericPoint Y) := by
  let T := Y.presheaf.stalk y
  let σ := StalkImage.map i y x h
  have hs := Local.SupportSpectrum.stalkMap_square i y x h
  have he := congrArg (fun f : Spec T ⟶ X => f (genericPoint (Spec T))) hs
  change X.fromSpecStalk x ((Spec.map σ) (genericPoint (Spec T))) =
    i (Y.fromSpecStalk y (genericPoint (Spec T))) at he
  rw [Stalk.Localization.genericPoint_image, genericPoint_eq_bot_of_affine] at he
  exact he

theorem height [IsLocallyNoetherian X] :
    (prime i y x h).asIdeal.height = Order.coheight (i (genericPoint Y)) := by
  rw [Stalk.Localization.height_eq_coheight_image, image]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.StalkImage
