import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementQuasiIso
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic

/-! # Base Cech Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechCoverRefinement

noncomputable section

/-! The original base-linear Čech refinement on arbitrary affine
covers is a quasi-isomorphism for quasicoherent modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite Simplicial
open Scheme.Modules

universe u
variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι κ : Type u} (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (M : X.Modules)

private abbrev forget : ModuleCat.{u} Γ(S, ⊤) ⥤ AddCommGrpCat.{u} := forget₂ _ _
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechCoverRefinement.forget (S := S)
local notation "P" => OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M

def map : AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U ⟶ AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M V :=
  GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r P

def forgetIso {ι : Type u} (U : ι → X.Opens) :
    ((G).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U) ≅
      (cechComplexFunctor U).obj M.presheaf :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech P

theorem forget_natural :
    ((G).mapHomologicalComplex (.up ℕ)).map (BaseCechCoverRefinement.map π U V r M) ≫ (forgetIso π M V).hom =
      (forgetIso π M U).hom ≫ Cech.CoverRefinement.map U V r M.presheaf := by
  apply HomologicalComplex.hom_ext
  intro n
  change (G).map ((BaseCechCoverRefinement.map π U V r M).f n) ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk κ V).cech P).hom.f n =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech P).hom.f n ≫ _
  rw [AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f, AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f]
  let En := (FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)
  let Em := (FormalCoproduct.mk κ V).cech.obj (op ⦋n⦌)
  let a := (FormalCoproduct.cechFunctor.map r).app (op ⦋n⦌)
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.piComparison_natural G
    (fun i : En.I => (P).obj (op (En.obj i)))
    (fun i : Em.I => (P).obj (op (Em.obj i))) a.f (fun i => (P).map (a.φ i).op)

def homologyIso {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (G).obj ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology n) ≅
      ((cechComplexFunctor U).obj M.presheaf).homology n :=
  (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).sc n).mapHomologyIso G).symm ≪≫
    HomologicalComplex.homologyMapIso (forgetIso π M U) n

theorem homology_natural (n : ℕ) :
    (G).map (HomologicalComplex.homologyMap (BaseCechCoverRefinement.map π U V r M) n) ≫ (homologyIso π M V n).hom =
      (homologyIso π M U n).hom ≫
        HomologicalComplex.homologyMap (Cech.CoverRefinement.map U V r M.presheaf) n :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.naturality G (.up ℕ)
    (forgetIso π M U) (forgetIso π M V) (BaseCechCoverRefinement.map π U V r M)
    (Cech.CoverRefinement.map U V r M.presheaf) (forget_natural π U V r M) n

variable [X.IsSeparated] [M.IsQuasicoherent]

theorem quasiIso (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i)) :
    QuasiIso (BaseCechCoverRefinement.map π U V r M) := by
  have hq : QuasiIso (Cech.CoverRefinement.map U V r M.presheaf) :=
    Cech.CoverRefinementQuasiIso.quasiIso U V r ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) hU hV
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic M U haU)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic M V haV)
  rw [_root_.quasiIso_iff]
  intro n
  let : IsIso (HomologicalComplex.homologyMap (Cech.CoverRefinement.map U V r M.presheaf) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have he : (G).map (HomologicalComplex.homologyMap (BaseCechCoverRefinement.map π U V r M) n) =
      (homologyIso π M U n).hom ≫
        HomologicalComplex.homologyMap (Cech.CoverRefinement.map U V r M.presheaf) n ≫
        (homologyIso π M V n).inv := by
    apply (cancel_mono (homologyIso π M V n).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using homology_natural π U V r M n
  have : IsIso ((G).map (HomologicalComplex.homologyMap (BaseCechCoverRefinement.map π U V r M) n)) := by
    rw [he]
    infer_instance
  exact isIso_of_reflects_iso (HomologicalComplex.homologyMap (BaseCechCoverRefinement.map π U V r M) n) G

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechCoverRefinement
