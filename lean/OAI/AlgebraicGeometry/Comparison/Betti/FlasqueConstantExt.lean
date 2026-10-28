import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Injective
import OAI.AlgebraicGeometry.Comparison.Betti.ConstantSheafSections
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomologyExt

/-! # Flasque Constant Ext -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueConstantExt

noncomputable section

/-! Flasque complex sheaves have no higher Ext from the actual constant complex sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace

variable {X : TopCat.{0}} (F : ConstantSheafSections.ComplexSheaves X) [TopCat.Sheaf.IsFlasque F]

local instance constantFlasqueExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves X) := HasExt.standard _

theorem singleComplex_flasque (n : ℕ) :
    TopCat.Sheaf.IsFlasque (((CochainComplex.single₀ (ConstantSheafSections.ComplexSheaves X)).obj F).X n) := by
  cases n with
  | zero => exact inferInstanceAs (TopCat.Sheaf.IsFlasque F)
  | succ n =>
      exact FlasqueNatQuasiIso.flasque_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 F (n + 1) (by omega))

theorem flasqueInjective_sections_exactAt_succ (n : ℕ) :
    (((FlasqueBiproduct.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution F).cocomplex).ExactAt (n + 1) := by
  let I := injectiveResolution F
  let S := (CochainComplex.single₀ (ConstantSheafSections.ComplexSheaves X)).obj F
  let H := (FlasqueBiproduct.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)
  have hq : QuasiIso (H.map I.ι) := FlasqueNatQuasiIso.nat_sections_quasiIso I.ι
    (singleComplex_flasque F)
    (fun q => @InjectiveFlasque.injective_flasque X (I.cocomplex.X q) (I.injective q)) I.quasiIso ⊤
  have hz : IsZero ((H.obj S).X (n + 1)) :=
    (FlasqueBiproduct.sections (⊤ : Opens X)).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 F (n + 1) (by omega))
  have he : (H.obj S).ExactAt (n + 1) := ShortComplex.exact_of_isZero_X₂ _ hz
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (he.isZero_homology.of_iso (isoOfQuasiIsoAt (H.map I.ι) (n + 1)).symm)

theorem flasqueConstantExt_subsingleton (n : ℕ) :
    Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf X) F (n + 1)) := by
  let I : InjectiveResolution F := injectiveResolution F
  have h := (flasqueInjective_sections_exactAt_succ F n).of_iso
    (ConstantSheafSections.constantHomSectionsComplexIso I.cocomplex).symm
  have hz : IsZero ((InjectiveHomologyExt.homSectionsComplex (C := ConstantSheafSections.ComplexSheaves X) (R := ℂ) I
      (ConstantSheafSections.standardConstantSheaf X)).homology (n + 1)) := h.isZero_homology
  have hs : Subsingleton ((InjectiveHomologyExt.homSectionsComplex (C := ConstantSheafSections.ComplexSheaves X) (R := ℂ) I
      (ConstantSheafSections.standardConstantSheaf X)).homology (n + 1)) := ModuleCat.subsingleton_of_isZero hz
  exact (InjectiveHomologyExt.homologyExtLinearEquiv (C := ConstantSheafSections.ComplexSheaves X) (R := ℂ)
    (X := ConstantSheafSections.standardConstantSheaf X) I (n + 1)).symm.injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueConstantExt
