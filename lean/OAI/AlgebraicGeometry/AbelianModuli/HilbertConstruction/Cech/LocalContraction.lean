/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafLocalContraction.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionFaces

/-! # Local Contraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContraction.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {ι : Type u}
variable (U : ι → Opens X)
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

theorem cechLocalContraction_differential_component {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ)
    (s : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op V))
    (hs : (SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) s = 0)
    (i : Fin (n + 2) → ι) :
    IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V
        ((SheafDifferential.IntrinsicCech.cechDifferential F U n).hom.app (op V)
          (LocalContractionSections.IntrinsicCech.cechLocalContraction U F i₀ hV n s)) i =
      IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V s i := by
  rw [SheafDifferential.IntrinsicCech.cechDifferential_apply]
  change (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    LocalContractionSections.IntrinsicCech.cechFaceSection U F n V (LocalContractionSections.IntrinsicCech.cechLocalContraction U F i₀ hV n s) k i) = _
  have hd := congrArg (fun y =>
    IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 2) V y (LocalContractionIndices.IntrinsicCech.cechPrependIndex i₀ i)) hs
  rw [SheafDifferential.IntrinsicCech.cechDifferential_apply] at hd
  simp only [map_zero, Pi.zero_apply] at hd
  change (∑ k : Fin (n + 3), (-1 : ℤ) ^ (k : ℕ) •
    LocalContractionSections.IntrinsicCech.cechFaceSection U F (n + 1) V s k (LocalContractionIndices.IntrinsicCech.cechPrependIndex i₀ i)) = 0 at hd
  have hd' := congrArg (fun y => F.obj.map (eqToHom (congrArg op
    (LocalContractionIndices.IntrinsicCech.cechPrependIntersection_eq U i₀ hV i))) y) hd
  simp only [map_zero] at hd'
  rw [map_sum, Fin.sum_univ_succ] at hd'
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
    mul_neg, mul_one, neg_smul, map_neg, map_zsmul,
    LocalContractionFaces.IntrinsicCech.cechFaceSection_zero_transport U F i₀ hV n s i,
    LocalContractionFaces.IntrinsicCech.cechFaceSection_succ_transport U F i₀ hV n s i] at hd'
  rw [Finset.sum_neg_distrib] at hd'
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hd')).symm

/-- A positive-degree Cech cycle on an open contained in one cover member has a
preimage under the preceding Cech differential. -/
theorem exists_preimage_cechDifferential_of_le {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ)
    (s : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op V))
    (hs : (SheafDifferential.IntrinsicCech.cechDifferential F U (n + 1)).hom.app (op V) s = 0) :
    ∃ t : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op V),
      (SheafDifferential.IntrinsicCech.cechDifferential F U n).hom.app (op V) t = s := by
  refine ⟨LocalContractionSections.IntrinsicCech.cechLocalContraction U F i₀ hV n s,
    (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V).injective ?_⟩
  funext i
  exact cechLocalContraction_differential_component U F i₀ hV n s hs i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContraction.IntrinsicCech
