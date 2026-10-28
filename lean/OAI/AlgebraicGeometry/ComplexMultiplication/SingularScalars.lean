import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.ScalarCompatibility
import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Singular
import OAI.AlgebraicTopology.Singular.GlobalRestriction
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Singular Scalars -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularScalars

noncomputable section

/-! # Scalar maps on raw and sheafified global singular cochains -/

open _root_.CategoryTheory Limits OAI.AlgebraicTopology.Singular

variable (R : Type) [CommRing R] (Y : TopCat.{0}) (q : R)

/-- The actual coefficient scalar map evaluated on the top open. -/
def rawGlobalSingularScalar :
    AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y ⟶ AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y :=
  (((evaluation (TopologicalSpace.Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (Coefficient.Scalars.singularCochainPresheafComplexScalar R Y q)

/-- Global sections of the sheafified coefficient scalar map. -/
def sheafGlobalSingularScalar :
    AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R Y ⟶ AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R Y :=
  ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (Coefficient.Scalars.singularCochainSheafComplexScalar R Y q)

set_option backward.isDefEq.respectTransparency false in
/-- The original global comparison commutes with the original coefficient scalar maps. -/
lemma rawGlobalSingularScalar_comparison :
    rawGlobalSingularScalar R Y q ≫ AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R Y =
      AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R Y ≫ sheafGlobalSingularScalar R Y q := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, AlgebraicTopology.Singular.GlobalRestriction.topOpenToGlobalSingularCochainSheafComplex_f]
  change (Coefficient.Scalars.singularCochainPresheafScalar R Y q n).app (.op ⊤) ≫
      (toSheafify (Opens.grothendieckTopology Y) (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R Y n)).app (.op ⊤) =
    (toSheafify (Opens.grothendieckTopology Y) (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R Y n)).app (.op ⊤) ≫
      (sheafifyMap (Opens.grothendieckTopology Y) (Coefficient.Scalars.singularCochainPresheafScalar R Y q n)).app
        (.op ⊤)
  exact congrArg (fun f => f.app (.op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology Y)
      (Coefficient.Scalars.singularCochainPresheafScalar R Y q n))

/-- Homology of a linear complex sends the scalar multiple of a map to that scalar multiple. -/
lemma moduleComplex_homologyMap_smul {K L : CochainComplex (ModuleCat R) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (q • f) n = q • HomologicalComplex.homologyMap f n := by
  change ShortComplex.homologyMap (q • ((HomologicalComplex.shortComplexFunctor
    (ModuleCat R) (ComplexShape.up ℕ) n).map f)) = _
  exact ShortComplex.homologyMap_smul _ q

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularScalars
