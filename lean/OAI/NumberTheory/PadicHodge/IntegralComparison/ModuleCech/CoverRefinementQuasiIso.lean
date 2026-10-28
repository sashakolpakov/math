import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementQuasiIso

/-! # Cover Refinement Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinementQuasiIso

noncomputable section

/-! The literal affine-cover refinement map is a quasi-isomorphism for
quasicoherent modules in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (M : X.left.Modules)
  [X.left.IsSeparated] [M.IsQuasicoherent]
  (hU : iSup U = ⊤) (hV : iSup V = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))

include hU hV haU haV in
theorem quasiIso : QuasiIso (CoverRefinement.map R X U V r M) := by
  let G := CohomologyNaturality.forgetCoefficients R
  let F := (SheafOfModules.toSheaf X.left.ringCatSheaf).obj M
  have hq : QuasiIso (Cech.CoverRefinement.map U V r M.presheaf) :=
    Cech.CoverRefinementQuasiIso.quasiIso U V r F hU hV
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic M U haU)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic M V haV)
  rw [_root_.quasiIso_iff]
  intro n
  let : IsIso (HomologicalComplex.homologyMap (Cech.CoverRefinement.map U V r M.presheaf) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h := CoverRefinement.forget_homology_natural R X U V r M n
  have he : G.map (HomologicalComplex.homologyMap (CoverRefinement.map R X U V r M) n) =
      (CohomologyNaturality.forgetHomologyIso R X U M n).hom ≫
        HomologicalComplex.homologyMap (Cech.CoverRefinement.map U V r M.presheaf) n ≫
        (CohomologyNaturality.forgetHomologyIso R X V M n).inv := by
    apply (cancel_mono (CohomologyNaturality.forgetHomologyIso R X V M n).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  have : IsIso (G.map (HomologicalComplex.homologyMap (CoverRefinement.map R X U V r M) n)) := by
    rw [he]
    infer_instance
  exact isIso_of_reflects_iso (HomologicalComplex.homologyMap (CoverRefinement.map R X U V r M) n) G

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinementQuasiIso
