import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechResolution
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.AffineCechAcyclic
import OAI.AlgebraicGeometry.Comparison.Betti.TotalCohomologyAcyclic
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantExt
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! # Cech Acyclic Terms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechAcyclicTerms

noncomputable section

/-! The actual finite affine Čech–de Rham total resolution has Ext-acyclic terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

local instance : HasExt.{1} (HypercohomologyForget.AdditiveZariskiSheaves X) := HasExt.standard _
local instance : HasExt.{0} (HypercohomologyForget.AdditiveZariskiSheaves X) :=
  inferInstanceAs (HasExt.{0} (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0}))

include hU in
theorem algebraicCechBicomplex_term_acyclic (a b q : ℕ) :
    Subsingleton (Sheaf.H.{0} (J := Opens.grothendieckTopology X.left)
      (((Betti.Sheaf.CechAugmentation.sheafCechBicomplex U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X)).X a).X b) (q + 1)) := by
  change Subsingleton (Sheaf.H.{0} (J := Opens.grothendieckTopology X.left)
    (((Betti.Sheaf.CechFunctor.sheafCechResolutionFunctor U).obj ((AdditiveComplexExtension.algebraicAdditiveSheafComplex X).X a)).X b)
    (q + 1))
  rw [AdditiveComplexExtension.algebraicAdditiveSheafComplex_X]
  exact Betti.Finite.AffineCechAcyclic.finiteAffineCech_algebraicForms_term_acyclic X U hU a b q

include hU in
theorem algebraicCechTotalComplex_term_acyclic (n q : ℕ) :
    Subsingleton (Sheaf.H.{0} (J := Opens.grothendieckTopology X.left) ((CechResolution.algebraicCechTotalComplex X U).X n) (q + 1)) := by
  let K : HomologicalComplex₂
      (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0}) (.up ℕ) (.up ℕ) :=
    Betti.Sheaf.CechAugmentation.sheafCechBicomplex U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X)
  have : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
    change Finite {p : ℕ × ℕ // p.1 + p.2 = n}
    exact Betti.Finite.TotalDiagonal.finiteTotalDiagonal n
  let D := K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n
  have hD : CategoryTheory.Limits.HasCoproduct D := (TotalExists.hasTotal_of_finiteCoproducts K) n
  exact @Betti.Finite.CoproductCohomology.Cech.finiteCoproduct_cohomology_subsingleton
    (TopCat.of X.left) _ inferInstance D hD (q + 1)
    (fun p => algebraicCechBicomplex_term_acyclic X U hU p.val.1 p.val.2 q)

include hU in
theorem algebraicCechTotalComplexInt_term_acyclic (n : ℤ) (q : ℕ) :
    Subsingleton (Sheaf.H.{0} (J := Opens.grothendieckTopology X.left) ((CechResolution.algebraicCechTotalComplexInt X U).X n) (q + 1)) := by
  let H := Sheaf.functorH.{0} (Opens.grothendieckTopology X.left) (q + 1)
  cases n with
  | ofNat n =>
    have : Subsingleton (H.obj ((CechResolution.algebraicCechTotalComplex X U).X n)) :=
      algebraicCechTotalComplex_term_acyclic X U hU n q
    let e := H.mapIso ((CechResolution.algebraicCechTotalComplex X U).extendXIso
      (ComplexShape.embeddingUpIntGE 0)
      (show (ComplexShape.embeddingUpIntGE 0).f n = (n : ℤ) by simp))
    exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton
  | negSucc n =>
    exact Sheaf.subsingleton_H_of_isZero
      ((CechResolution.algebraicCechTotalComplexInt X U).isZero_of_isStrictlyGE 0 (Int.negSucc n) (by omega))
      (q + 1)

include hU in
theorem algebraicCechTotalComplexInt_termExt_acyclic (n : ℤ) (q : ℕ) :
    Subsingleton (Ext.{1} (AdditiveConstantExt.Cech.constantIntegers (TopCat.of X.left))
      ((CechResolution.algebraicCechTotalComplexInt X U).X n) (q + 1)) :=
  AdditiveConstantExt.Cech.constantIntegerExt_subsingleton (TopCat.of X.left) _ (q + 1)
    (algebraicCechTotalComplexInt_term_acyclic X U hU n q)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechAcyclicTerms
