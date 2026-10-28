import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFunctions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.Neighborhoods
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Normalized Local Fiber -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFiber.Construction

noncomputable section

/-! The initial infinitesimal neighborhood of the actual local normalization family is its actual scheme fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (n : f.normalization)

/-- The zeroth infinitesimal scheme is literally the residue-field fiber, up to the canonical
pullback-pasting isomorphism and the equality m^1 = m. -/
def normalizedLocalInitialFiberIso :
    Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood (IsLocalRing.maximalIdeal (f.normalization.presheaf.stalk n))
      (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) 0 ≅ f.toNormalization.fiber n := by
  let R := f.normalization.presheaf.stalk n
  let I := IsLocalRing.maximalIdeal R
  let e : CommRingCat.of (R ⧸ I ^ (0 + 1)) ≅ f.normalization.residueField n :=
    (Ideal.quotEquivOfEq (show I ^ (0 + 1) = I by simp)).toCommRingCatIso
  let h : Infinitesimal.Neighborhoods.Construction.infinitesimalBase I 0 ⟶ Spec (f.normalization.residueField n) := Spec.map e.inv
  have hh : h ≫ Spec.map (f.normalization.residue n) = Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I 0 := by
    change Spec.map e.inv ≫ Spec.map (f.normalization.residue n) = _
    rw [← Spec.map_comp]
    congr 1
  have : IsIso h := inferInstanceAs (IsIso (Spec.map e.inv))
  let a : Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood I (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) 0 ⟶
      pullback (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) (Spec.map (f.normalization.residue n)) :=
    pullback.map _ _ _ _ (𝟙 _) h (𝟙 _) (by simp) (by simp [hh])
  have : IsIso a := by dsimp [a]; infer_instance
  exact asIso a ≪≫ pullbackLeftPullbackSndIso f.toNormalization
    (f.normalization.fromSpecStalk n) (Spec.map (f.normalization.residue n))

/-- Connectedness of the actual initial infinitesimal scheme gives connectedness of the
actual fiber of the normalization map. -/
theorem normalized_fiber_connected_of_local_initial_connected
    [ConnectedSpace (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood
      (IsLocalRing.maximalIdeal (f.normalization.presheaf.stalk n)) (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) 0)] :
    ConnectedSpace (f.toNormalization.fiber n) := by
  let e := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (normalizedLocalInitialFiberIso f n))
  exact e.connectedSpace_iff.mp inferInstance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFiber.Construction
