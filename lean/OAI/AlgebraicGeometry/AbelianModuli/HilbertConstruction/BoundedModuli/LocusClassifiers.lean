import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ClassifierConditions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.LevelIsomorphismParameters

/-! # Locus Classifiers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli

noncomputable section

/-! Every bounded complete moduli isomorphism has compatible classifier points in the polarization and full-level loci. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
variable {T : Over S} (e : IsomorphismFunctor.BoundedFamilyLevelIso A B j P T)

def IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier : T ⟶ Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameter A.polarization B.polarization j P :=
  (Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameterPointEquiv A.polarization B.polarization j P T).symm
    ⟨IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e, (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_conditions A B j P PB e).1⟩

omit [NeZero N] in
theorem IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier_comp :
    IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier A B j P PB e ≫ Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P =
      IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e :=
  congrArg Subtype.val ((Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameterPointEquiv A.polarization B.polarization j P T).apply_symm_apply
    ⟨IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e, (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_conditions A B j P PB e).1⟩)

def IsomorphismFunctor.BoundedFamilyLevelIso.fullLevelClassifier : T ⟶ Bounded.LevelIsomorphismParameters.boundedFullLevelIsoParameter A.abelian B.abelian A.level B.level j P :=
  (Bounded.LevelIsomorphismParameters.boundedFullLevelIsoParameterPointEquiv A.abelian B.abelian A.level B.level j P T).symm
    ⟨IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e, (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_conditions A B j P PB e).2⟩

theorem IsomorphismFunctor.BoundedFamilyLevelIso.fullLevelClassifier_comp :
    IsomorphismFunctor.BoundedFamilyLevelIso.fullLevelClassifier A B j P PB e ≫ Bounded.LevelIsomorphismParameters.boundedFullLevelIsoParameterInclusion A.abelian B.abelian A.level B.level j P =
      IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e :=
  congrArg Subtype.val ((Bounded.LevelIsomorphismParameters.boundedFullLevelIsoParameterPointEquiv A.abelian B.abelian A.level B.level j P T).apply_symm_apply
    ⟨IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e, (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_conditions A B j P PB e).2⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli
