import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldExternalFirstCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointCohomologyEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NontrivialPoincarePointSections

/-! # Nontrivial Poincare Point Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A nonidentity dual point has zero genuine cohomology in every degree. The proof uses the actual addition retraction and the external tensor square, with finite frame covers supplied by properness. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)
variable (f : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme) (hf : f ≠ 1)

include hf in
theorem Dual.Data.DualAbelianData.poincarePointBundle_cohomology_vanish (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (D.poincarePointBundle f).sheaf q) := by
  have hsections : Subsingleton Γ((D.poincarePointBundle f).sheaf, ⊤) := by
    have h := ModuleCat.subsingleton_of_isZero (D.poincarePointBundle_sections_isZero f hf)
    exact h
  have H : IsPullback (fst A.scheme A.scheme).left (snd A.scheme A.scheme).left
      A.scheme.hom A.scheme.hom := IsPullback.of_hasPullback A.scheme.hom A.scheme.hom
  induction q using Nat.strong_induction_on with
  | h q ih =>
    cases q with
    | zero =>
      constructor
      intro x y
      apply (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections (D.poincarePointBundle f).sheaf).injective
      exact @Subsingleton.elim _ hsections _ _
    | succ n =>
      have hprod : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
          (Graph.ExternalTensorBundle.externalTensorBundle (A := A.scheme) (B := A.scheme)
            (D.poincarePointBundle f) (D.poincarePointBundle f)).sheaf (n + 1)) :=
        Proper.FieldExternalFirstCohomology.properFieldExternalTensor_firstCohomology_vanish H
          (D.poincarePointBundle f) (D.poincarePointBundle f) n ih hsections
      constructor
      intro x y
      apply D.poincarePointBundle_externalSquareCohomologyMap_injective f (n + 1)
      exact @Subsingleton.elim _ hprod _ _

include hf in
theorem Dual.Data.DualAbelianData.poincarePointBundle_cohomology_isZero (q : ℕ) :
    IsZero ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor A.scheme.left q).obj
      (D.poincarePointBundle f).sheaf) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact D.poincarePointBundle_cohomology_vanish f hf q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
