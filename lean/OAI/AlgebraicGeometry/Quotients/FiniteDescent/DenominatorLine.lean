import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorNeighborhoodLe
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.StalkIdealFrame

/-! # Denominator Line -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorLine.Construction.DenominatorLineBundle

noncomputable section

/-! The actual line bundle of denominators of a rational function on a smooth integral scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X]

def stalkIdeals (r : X.functionField) (x : X) : Ideal (X.presheaf.stalk x) :=
  DenominatorIdealEq.Construction.DenominatorIdeal.ideal r

theorem stalk_generator (r : X.functionField) (U : X.affineOpens) (a : Γ(X, U))
    (ha : (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a}) (x : U.1) :
    stalkIdeals r x = Ideal.span {X.presheaf.germ U.1 x x.2 a} := by
  change DenominatorIdealEq.Construction.DenominatorIdeal.ideal (R := X.presheaf.stalk x) r = _
  rw [← DenominatorStalkIs.Construction.DenominatorStalk.map_stalk r U x, ha, Ideal.map_span, Set.image_singleton]

theorem generator_mem (r : X.functionField) (U : X.affineOpens) (a : Γ(X, U))
    (ha : (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a}) :
    a ∈ StalkIdealIs.Construction.StalkIdealSheaf.ideal (stalkIdeals r) U.1 := by
  apply (StalkIdealIs.Construction.StalkIdealSheaf.mem_ideal _ _ _).mpr
  intro x
  rw [stalk_generator r U a ha x]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem generator_ne_zero (r : X.functionField) (U : X.affineOpens) [Nonempty U.1]
    (a : Γ(X, U)) (ha : (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a}) : a ≠ 0 := by
  intro ha0
  have := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  apply DenominatorIdealEq.Construction.DenominatorIdeal.ne_bot (R := Γ(X, U)) r
  change DenominatorSheafEq.Construction.DenominatorSheaf.affineIdeal r U = Ideal.span {a} at ha
  rw [DenominatorSheafEq.Construction.DenominatorSheaf.affineIdeal_eq, ha0] at ha
  simpa using ha

def lineBundle {K : Type u} [Field K] [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [Smooth f] (r : X.functionField) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := StalkIdealIs.Construction.StalkIdealSheaf.sheaf (stalkIdeals r)
  locallyTrivial x := by
    obtain ⟨U, hxU, a, ha⟩ := DenominatorNeighborhoodLe.Construction.DenominatorNeighborhood.exists_principal f r x
    have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    change (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U = Ideal.span {a} at ha
    exact ⟨U.1, hxU, ⟨StalkIdealFrame.Construction.StalkIdealFrames.frameIso (stalkIdeals r) U.1 a
      (generator_mem r U a ha) (generator_ne_zero r U a ha) (stalk_generator r U a ha)⟩⟩

def inclusion {K : Type u} [Field K] [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [Smooth f] (r : X.functionField) :
    (lineBundle f r).sheaf ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  StalkIdealIs.Construction.StalkIdealSheaf.inclusion (stalkIdeals r)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorLine.Construction.DenominatorLineBundle
