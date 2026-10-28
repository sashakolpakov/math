import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizationEqualityParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismCompositionLaws
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismEquality

/-! # Polarization Point Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizationPointCriterion

noncomputable section

/-! The closed polarization condition is exactly the commuting polarization square on the original families pulled back to each test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g n : ℕ} {δ : Fin g → ℕ}
variable {A B : Abelian.Schemes.AbelianScheme g S} {D : Dual.Data.DualAbelianData A} {E : Dual.Data.DualAbelianData B}
variable (p : PolarizationData.Polarization D δ) (q : PolarizationData.Polarization E δ)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

theorem boundedPolarization_test_iff {T : Over S} (c : T ⟶ IsoParameters.boundedAbelianIsoParameter A B j P) :
    (Over.pullback c.left).map (PolarizationEqualityParameters.boundedPolarizationLeft p j P) =
      (Over.pullback c.left).map (PolarizationEqualityParameters.boundedPolarizationRight q j P) ↔
    (p.pullback T.hom).isogeny.hom ≫
        Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (UniversalDualIsomorphism.boundedAbelianUniversalDualIso D E j P).hom =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (UniversalIso.boundedAbelianUniversalIso A B j P).hom ≫
        (q.pullback T.hom).isogeny.hom := by
  have h := (Geometric.MorphismEquality.geometricFamilyMorphismBaseChange_eq_iff c
    (PolarizationEqualityParameters.boundedPolarizationLeft p j P) (PolarizationEqualityParameters.boundedPolarizationRight q j P)).symm
  have hL : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (PolarizationEqualityParameters.boundedPolarizationLeft p j P) =
      (p.pullback T.hom).isogeny.hom ≫
        Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (UniversalDualIsomorphism.boundedAbelianUniversalDualIso D E j P).hom :=
    (Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_map_comp c
      ((Over.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).map p.isogeny.hom)
      (UniversalDualIsomorphism.boundedAbelianUniversalDualIso D E j P).hom).trans
      (congrArg (fun w => w ≫ Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (UniversalDualIsomorphism.boundedAbelianUniversalDualIso D E j P).hom)
        (Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_original c p.isogeny.hom))
  have hR : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (PolarizationEqualityParameters.boundedPolarizationRight q j P) =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (UniversalIso.boundedAbelianUniversalIso A B j P).hom ≫
        (q.pullback T.hom).isogeny.hom :=
    (Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_map_comp c (UniversalIso.boundedAbelianUniversalIso A B j P).hom
      ((Over.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).map q.isogeny.hom)).trans
      (congrArg (fun w => Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (UniversalIso.boundedAbelianUniversalIso A B j P).hom ≫ w)
        (Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_original c q.isogeny.hom))
  exact h.trans (congrArg₂ (fun a b => a = b) hL hR).to_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizationPointCriterion
