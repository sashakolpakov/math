import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Morphism Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MorphismDescent

noncomputable section

/-! Flatness itself descends under faithfully flat quasi-compact base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u

private theorem flat_of_faithfullyFlat_tensor (R B A : Type u)
    [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
    (hB : (algebraMap R B).FaithfullyFlat)
    (hA : (algebraMap B (B ⊗[R] A)).Flat) : (algebraMap R A).Flat := by
  have : Module.FaithfullyFlat R B := (RingHom.faithfullyFlat_algebraMap_iff).mp hB
  have : Module.Flat B (B ⊗[R] A) := (RingHom.flat_algebraMap_iff).mp hA
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_flat_tensorProduct R A B)

/-- Flat ring maps descend along faithfully flat ring maps. -/
theorem ringFlat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  apply RingHom.CodescendsAlong.mk _ RingHom.Flat.respectsIso
  exact flat_of_faithfullyFlat_tensor

/-- Flat scheme morphisms descend under faithfully flat quasi-compact base change. -/
instance flat_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@Flat.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat ringFlat_codescendsAlong_faithfullyFlat

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MorphismDescent
