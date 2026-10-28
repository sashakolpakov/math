import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.Classifier
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Recovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.PreservationRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizationEqualityParameters

/-! # Classifier Conditions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli

noncomputable section

/-! The ambient classifier of every bounded complete moduli isomorphism satisfies the defining polarization and full-level equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_conditions
    {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) {T : Over S}
    (e : IsomorphismFunctor.BoundedFamilyLevelIso A B j P T) :
    (Over.pullback (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e).left).map (Bounded.PolarizationEqualityParameters.boundedPolarizationLeft A.polarization j P) =
      (Over.pullback (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e).left).map (Bounded.PolarizationEqualityParameters.boundedPolarizationRight B.polarization j P) ∧
    Level.PreservationProperties.FullLevelPreservesPullback
      (A.level.pullback (Bounded.IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P).hom)
      (B.level.pullback (Bounded.IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P).hom)
      (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e).left := by
  let M := Bounded.IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P
  let c := IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e
  let q := (Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv A B c).symm e.val
  have hq : q.abelian.hom = (Over.pullback c.left).map (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom :=
    Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv_symm_abelian_hom A B c e.val
      (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_recovers A B j P e)
  exact Moduli.Isomorphisms.LevelPreservingIso.pullback_preservation_conditions (A.pullback M.hom) (B.pullback M.hom)
    (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom
    (Bounded.UniversalDualIsomorphism.boundedAbelianUniversalDualIso A.dual B.dual j P).hom
    (Bounded.UniversalDualIsomorphism.boundedAbelianUniversalDualIso_poincare A.dual B.dual j P PB) c.left q hq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli
