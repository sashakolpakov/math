import OAI.AlgebraicGeometry.SheafCohomology.LineBundleLocalGenerators

/-! # Finite Presentation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.FinitePresentation.Projective

noncomputable section

/-! Finite local presentations of the actual ProjectiveCohomology line-bundle sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- Finite presentation of the original local data from the chosen rank-one frames. -/
abbrev lineBundlePresentationFinite (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) : Prop :=
  (LineBundleLocalGenerators.Projective.lineBundleLocalGenerators A L).quasiCoherentData.IsFinitePresentation

/-- The usual finite-presentation property, specialized to a scheme module. -/
abbrev schemeModuleFinitePresentation (X : Scheme.{0}) (M : X.Modules) : Prop :=
  M.IsFinitePresentation

instance lineBundlePresentation_finite (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) :
    lineBundlePresentationFinite A L where
  isFinite_presentation _x := {
    isFiniteType_generators := LineBundleLocalGenerators.Projective.rankOneGenerators_finite _ _ _
    isFiniteType_relations := { finite := inferInstanceAs (Finite (ULift Empty)) } }

/-- A line bundle has one local generator and no relations, hence is finitely presented. -/
instance lineBundleSheaf_finitePresentation (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) :
    schemeModuleFinitePresentation A.carrier L.sheaf :=
  ⟨(LineBundleLocalGenerators.Projective.lineBundleLocalGenerators A L).quasiCoherentData, inferInstance⟩

instance tensorPower_finitePresentation (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) (n : ℕ) :
    schemeModuleFinitePresentation A.carrier (Sheaves.Projective.tensorPower A L n) :=
  lineBundleSheaf_finitePresentation A (TensorBundles.Projective.tensorPowerLineBundle A L n)

end

end OAI.AlgebraicGeometry.SheafCohomology.FinitePresentation.Projective
