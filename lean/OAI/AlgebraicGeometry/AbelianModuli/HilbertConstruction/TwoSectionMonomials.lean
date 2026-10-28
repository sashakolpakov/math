import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PowerCoordinates

/-! # Two Section Monomials -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TwoSectionMonomials

noncomputable section

/-! Actual monomials in two global sections, all in one prescribed tensor degree, have the expected powers of their ratio on a denominator chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {M : X.Modules}

def tensorDegreeCast (M : X.Modules) {n d : ℕ} (h : n = d) :
    TensorPower.PowerSheaf.tensorPowerModule M n ⟶ TensorPower.PowerSheaf.tensorPowerModule M d :=
  eqToHom (congrArg (TensorPower.PowerSheaf.tensorPowerModule M) h)

theorem tensorPowerSection_degreeCast (s : Line.Bundles.structureModule X ⟶ M) {n d : ℕ} (h : n = d) :
    TensorPower.Maps.tensorPowerSection s n ≫ tensorDegreeCast M h = TensorPower.Maps.tensorPowerSection s d := by
  subst d
  exact Category.comp_id _

def twoSectionMonomial (s t : Line.Bundles.structureModule X ⟶ M) (d i : ℕ) (hi : i ≤ d) :
    Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule M d :=
  (TensorPower.Maps.tensorPowerSection t i ≫ Power.SectionTransitions.powerSectionTransition s i (d - i)) ≫
    tensorDegreeCast M (Nat.add_sub_of_le hi)

theorem twoSectionMonomial_localCoordinate (f : Y ⟶ X) [IsOpenImmersion f]
    (s t : Line.Bundles.structureModule X ⟶ M) [IsIso (Ample.LineBundles.pullbackSection f s)] (d i : ℕ) (hi : i ≤ d) :
    letI := Power.Nonvanishing.tensorPowerSection_pullback_isIso f s d
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s d))
      (Ample.LineBundles.pullbackSection f (twoSectionMonomial s t d i hi)) =
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) ^ i := by
  have (n : ℕ) : IsIso (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) :=
    Power.Nonvanishing.tensorPowerSection_pullback_isIso f s n
  exact (Power.SectionTransitions.frameCoordinate_pullback_postcomp f (TensorPower.Maps.tensorPowerSection s (i + (d - i)))
    (TensorPower.Maps.tensorPowerSection s d) (tensorDegreeCast M (Nat.add_sub_of_le hi))
    (tensorPowerSection_degreeCast s (Nat.add_sub_of_le hi))
    (TensorPower.Maps.tensorPowerSection t i ≫ Power.SectionTransitions.powerSectionTransition s i (d - i))).trans
      ((Power.SectionTransitions.frameCoordinate_powerSectionTransition f s i (d - i) (TensorPower.Maps.tensorPowerSection t i)).trans
        (Local.PowerCoordinates.frameCoordinate_local_tensorPower f i s t))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TwoSectionMonomials
