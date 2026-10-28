import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelUniversalConditions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledBackIsomorphismConstructor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Polarized Level Universal Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelUniversalIsomorphism

noncomputable section

/-! The combined parameter scheme carries an actual universal HilbertConstruction moduli isomorphism, with group laws, polarization, Poincare bundle, and full level all verified. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def boundedPolarizedLevelUniversalIteratedIso (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) :
    Moduli.Isomorphisms.LevelPreservingIso
      ((A.pullback (IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P).hom).pullback
        (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P).left)
      ((B.pullback (IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P).hom).pullback
        (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P).left) := by
  let M := IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P
  let i := PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P
  let e := UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P
  let d := UniversalDualIsomorphism.boundedAbelianUniversalDualIso A.dual B.dual j P
  have he : IsMonHom e.hom := UniversalIso.boundedAbelianUniversalIso_isMonHom A.abelian B.abelian j P
  have hd : IsMonHom d.hom := UniversalDualIsomorphism.boundedAbelianUniversalDualIso_isMonHom A.dual B.dual j P PD PE
  exact @Moduli.Isomorphisms.LevelPreservingIso.ofPullbackMaps M.left (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P).left g N δ
    (A.pullback M.hom) (B.pullback M.hom) e d he hd
    (UniversalDualIsomorphism.boundedAbelianUniversalDualIso_poincare A.dual B.dual j P PB) i.left
    (PolarizedLevelUniversalConditions.boundedPolarizedLevel_universal_polarization A B j P) (PolarizedLevelUniversalConditions.boundedPolarizedLevel_universal_level A B j P)

def boundedPolarizedLevelUniversalIso (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) :
    Moduli.Isomorphisms.LevelPreservingIso (A.pullback (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P).hom)
      (B.pullback (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P).hom) := by
  let M := IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P
  let i := PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P
  let e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback (i.left ≫ M.hom)) (B.pullback (i.left ≫ M.hom)) :=
    ((Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A M.hom i.left).symm.trans
      (boundedPolarizedLevelUniversalIteratedIso A B j P PB PD PE)).trans
      (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp B M.hom i.left)
  exact (congrArg (fun b => Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b)) i.w).mp e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelUniversalIsomorphism
