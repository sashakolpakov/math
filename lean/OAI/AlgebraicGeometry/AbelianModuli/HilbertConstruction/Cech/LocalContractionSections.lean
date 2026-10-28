/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafLocalContraction.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionIndices

/-! # Local Contraction Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionSections.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {ι : Type u}
variable (U : ι → Opens X)
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

noncomputable def cechLocalContraction {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ) (s : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op V)) :
    (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op V) :=
  (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V).symm fun i =>
    F.obj.map (eqToHom (congrArg op (LocalContractionIndices.IntrinsicCech.cechPrependIntersection_eq U i₀ hV i)))
      (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V s (LocalContractionIndices.IntrinsicCech.cechPrependIndex i₀ i))

theorem cechLocalContraction_apply {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ) (s : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op V))
    (i : Fin (n + 1) → ι) :
    IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V (cechLocalContraction U F i₀ hV n s) i =
      F.obj.map (eqToHom (congrArg op (LocalContractionIndices.IntrinsicCech.cechPrependIntersection_eq U i₀ hV i)))
        (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V s (LocalContractionIndices.IntrinsicCech.cechPrependIndex i₀ i)) := by
  rw [cechLocalContraction, AddEquiv.apply_symm_apply]

theorem cechTermSectionsAddEquiv_transport (n : ℕ) (V : Opens X)
    (s : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op V))
    {i j : Fin (n + 1) → ι} (h : i = j) :
    F.obj.map (eqToHom (congrArg
        (fun q : Fin (n + 1) → ι =>
          op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (q k))) h))
        (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V s i) =
      IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V s j := by
  subst h
  simp

noncomputable def cechFaceSection (n : ℕ) (V : Opens X)
    (s : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op V)) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) :
    F.obj.obj (op (V ⊓ ∏ᶜ fun a : Fin (n + 2) => U (i a))) :=
  F.obj.map (homOfLE (inf_le_inf_left V
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
    (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V s
      (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionSections.IntrinsicCech
