import OAI.AlgebraicGeometry.CycleClass.Thom.StalkRetractionScalars
import OAI.AlgebraicGeometry.CycleClass.Thom.FieldBaseStalk
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth Retract -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothRetract.Constructions

noncomputable section

/-! Smoothness at a point descends along an actual scheme retraction over
a field, proved by the scalar-compatible retraction on its local rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkRetractionScalars.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.FieldBaseStalk.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] {X Y : Scheme.{0}}

theorem stalkBaseMap_formallySmooth_iff (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFinitePresentation f] (x : X) :
    (StalkRetractionScalars.Constructions.stalkBaseMap f x).hom.FormallySmooth ↔ x ∈ f.smoothLocus := by
  let b := (Spec (CommRingCat.of K)).presheaf.germ ⊤ (f x) (by trivial)
  let : IsIso b := FieldBaseStalk.Constructions.fieldBase_germ_isIso K (f x)
  have hb : b ≫ f.stalkMap x = StalkRetractionScalars.Constructions.stalkBaseMap f x := by
    exact f.germ_stalkMap ⊤ x (by trivial)
  have h := RingHom.FormallySmooth.respectsIso.cancel_left_isIso b (f.stalkMap x)
  change (b ≫ f.stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.FormallySmooth at h
  rw [hb] at h
  exact h

theorem mem_smoothLocus_of_retract
    (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X)
    (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    (hi : i ≫ g = f) (hr : r ≫ f = g) (x : X)
    (hx : i x ∈ g.smoothLocus) : x ∈ f.smoothLocus := by
  apply (stalkBaseMap_formallySmooth_iff f x).mp
  exact StalkRetractionScalars.Constructions.stalkBaseMap_formallySmooth_of_retract i r h f g hr x hi
    ((stalkBaseMap_formallySmooth_iff g (i x)).mpr hx)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothRetract.Constructions
