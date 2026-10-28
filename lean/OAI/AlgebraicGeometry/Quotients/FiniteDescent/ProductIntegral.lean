import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Product Integral -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductIntegral

noncomputable section

/-! Products of proper geometrically integral families have integral
fibers, using the Cartesian product model of each residue-field fiber. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.ProductIntegralFibers

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
variable [IsProper f] [IsProper g] [Flat f]
variable [GeometricallyIntegral f] [GeometricallyIntegral g]

theorem integral (x : S) : IsIntegral ((pullback.fst f g ≫ f).fiber x) := by
  let t := S.fromSpecResidueField x
  let f' := f.fiberToSpecResidueField x
  let g' := g.fiberToSpecResidueField x
  have : IsProper f' := inferInstanceAs (IsProper (pullback.snd f t))
  have : IsProper g' := inferInstanceAs (IsProper (pullback.snd g t))
  have : Flat f' := inferInstanceAs (Flat (pullback.snd f t))
  have : GeometricallyIntegral f' := inferInstanceAs (GeometricallyIntegral (f.fiberToSpecResidueField x))
  have : IsIntegral (g.fiber x) := inferInstance
  have : IsLocallyNoetherian (g.fiber x) := LocallyOfFiniteType.isLocallyNoetherian g'
  have : IsIntegral (pullback f' g') := inferInstance
  let h := ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' (f.fiberι x) (g.fiberι x) t
    (IsPullback.of_hasPullback f t) (IsPullback.of_hasPullback g t)
  exact IsIntegral.of_isIso h.isoPullback.hom

end Construction.ProductIntegralFibers

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductIntegral
