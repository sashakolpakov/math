import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension

/-! # Relative Dimension Unique -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RelativeDimensionUnique

noncomputable section

/-! Relative smooth dimension over a perfect field is determined by
the local ring at any closed point of a nonempty scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
theorem eq {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [Nonempty X] (f : X ⟶ Spec (CommRingCat.of k))
    (n m : ℕ) [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] : n = m := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set X)) Set.univ_nonempty isClosed_univ.isLocallyClosed
  have hn := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension.Construction.ringKrullDim_stalk_of_smoothOfRelativeDimension n f x hx
  have hm := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension.Construction.ringKrullDim_stalk_of_smoothOfRelativeDimension m f x hx
  exact_mod_cast hn.symm.trans hm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RelativeDimensionUnique
