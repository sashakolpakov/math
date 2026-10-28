import OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedSectionExt
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCechIntersections

/-! # Affine Derived Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineDerivedSections.CrystallineAffineDerivedSections

noncomputable section

/-! # Derived sections on every proper Čech intersection have the actual completed affine computation -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
  {Y : Over (Spec (CommRingCat.of k))}
  (j : AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B ⟶ Y) [IsOpenImmersion j.left]

def affineIso (q : ℕ) :
    (GlobalCech.CrystallineGlobalCechCohomology.liftCoefficients p k).obj
      (((CrystallineZariski.SectionNaturality.CrystallineZariskiSectionNaturality.evaluation p k j).rightDerived q).obj
        (Site.structureSheaf p k Y)) ≅
          (Finite.Affine.FiniteAffineCrystalline.complex p k B).homology q :=
  DerivedSectionExt.CrystallineDerivedSectionExt.openIso p k j q ≪≫
    (Finite.Affine.FiniteAffineCrystalline.homologyIso p k B q).symm

variable (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
  (n : ℕ) (t : Fin (n + 1) → ProperCechIntersections.CrystallineProperCechIntersections.Index k X)

def intersectionIso (q : ℕ) :
    (GlobalCech.CrystallineGlobalCechCohomology.liftCoefficients p k).obj
      (((CrystallineZariski.SectionNaturality.CrystallineZariskiSectionNaturality.evaluation p k
        (ProperCechIntersections.CrystallineProperCechIntersections.inclusion k X n t)).rightDerived q).obj
          (Site.structureSheaf p k X)) ≅
            (Finite.Affine.FiniteAffineCrystalline.complex p k
              (ProperCechIntersections.CrystallineProperCechIntersections.coordinateRing k X n t)).homology q := by
  let j : AffineFrameCover.CrystallineAffineFrameCover.affineScheme k
      (ProperCechIntersections.CrystallineProperCechIntersections.coordinateRing k X n t) ⟶ X :=
    ProperCechIntersections.CrystallineProperCechIntersections.inclusion k X n t
  have : IsOpenImmersion j.left := ProperCechIntersections.CrystallineProperCechIntersections.inclusion_open k X n t
  exact affineIso p k (ProperCechIntersections.CrystallineProperCechIntersections.coordinateRing k X n t) j q

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineDerivedSections.CrystallineAffineDerivedSections
