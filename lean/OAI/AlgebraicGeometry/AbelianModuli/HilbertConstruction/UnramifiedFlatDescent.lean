import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Etale.Descent

/-! # Unramified Flat Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedFlatDescent

noncomputable section

/-! Formal unramifiedness descends along faithfully flat quasi-compact scheme base changes, using descent of the actual differential module. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

instance formallyUnramified_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@FormallyUnramified.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedFlatDescent
