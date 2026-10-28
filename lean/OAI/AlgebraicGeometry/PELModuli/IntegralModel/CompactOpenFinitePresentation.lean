import OAI.ArithmeticGeometry.Models.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Compact Open Finite Presentation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CompactOpenFinitePresentation

/-! Compact open subschemes retain finite presentation over an affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.ArithmeticGeometry.Models.Scheme.Constructions.Foundations

theorem compact_open_finitePresentation {S : Scheme.{0}} [IsAffine S] (X : Over S)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (U : X.left.Opens)
    (hU : IsCompact (U : Set X.left)) : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (U.ι ≫ X.hom) := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiSeparated X.hom := hX.2.2
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CompactOpenFinitePresentation
