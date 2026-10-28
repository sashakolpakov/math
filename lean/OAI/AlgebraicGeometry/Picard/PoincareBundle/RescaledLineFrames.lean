import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCoefficients
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

/-! # Rescaled Line Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RescaledLineFrames

noncomputable section

/-! Multiplying actual line frames by regular units and removing their multiplication coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCoefficients
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- Rescale an actual sheaf frame by an invertible regular function. -/
def rescale (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (r : Γ(X, ⊤)ˣ) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M :=
  s ≪≫ Isogenies.NeighborCounting.ModuleScalar.scalarIso M r

theorem rescale_one (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) : rescale s 1 = s := by
  apply Iso.ext
  change s.hom ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd M 1 = s.hom
  rw [Isogenies.NeighborCounting.ModuleScalar.scalarEnd_one, Category.comp_id]

theorem rescale_pullback {Y : Scheme.{u}} (f : Y ⟶ X)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (r : Γ(X, ⊤)ˣ) :
    FrameRatioPullback.pullFrame f (rescale s r) =
      rescale (FrameRatioPullback.pullFrame f s) (Units.map f.appTop.hom r) := by
  apply Iso.ext
  change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map (s.hom ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (r : Γ(X, ⊤))) =
    ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s.hom) ≫
      Isogenies.NeighborCounting.ModuleScalar.scalarEnd ((Scheme.Modules.pullback f).obj M) (f.appTop (r : Γ(X, ⊤)))
  rw [Functor.map_comp, Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback, Category.assoc]

theorem rescale_app_top (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (r : Γ(X, ⊤)ˣ) :
    (rescale s r).hom.app ⊤ (1 : Γ(X, ⊤)) =
      (r : Γ(X, ⊤)) • s.hom.app ⊤ (1 : Γ(X, ⊤)) := by
  change (Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (r : Γ(X, ⊤))).app ⊤ (s.hom.app ⊤ (1 : Γ(X, ⊤))) = _
  change X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) (r : Γ(X, ⊤)) •
    s.hom.app ⊤ (1 : Γ(X, ⊤)) = _
  rw [X.presheaf.map_id]
  rfl

/-- The coefficient equation gives equality of whole product frames after rescaling. -/
theorem product_rescale (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) [IsIso (Bilinear.BilinearPullback.toHom β)]
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P)
    (r s' t' : Γ(X, ⊤)ˣ) (h : MultiplicativeFrameCoefficients.coefficient β s t v * r * s' = t') :
    Bilinear.ProductFrames.productFrame β (rescale s r) (rescale t s') = rescale v t' := by
  apply Iso.ext
  apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P).injective
  change (Bilinear.ProductFrames.productFrame β (rescale s r) (rescale t s')).hom.app ⊤ (1 : Γ(X, ⊤)) =
    (rescale v t').hom.app ⊤ (1 : Γ(X, ⊤))
  rw [Bilinear.ProductFrames.productFrame_app]
  simp only [rescale_app_top]
  have hl := LinearMap.congr_fun ((β.app ⊤).map_smul
    (r : Γ(X, ⊤)) (s.hom.app ⊤ (1 : Γ(X, ⊤))))
    ((s' : Γ(X, ⊤)) • t.hom.app ⊤ (1 : Γ(X, ⊤)))
  erw [hl, LinearMap.smul_apply, map_smul, MultiplicativeFrameCoefficients.coefficient_action β s t v, smul_smul, smul_smul]
  have hh := congrArg (fun a : Γ(X, ⊤) => a • v.hom.app ⊤ (1 : Γ(X, ⊤))) (congrArg Units.val h)
  simpa only [Units.val_mul, mul_assoc, mul_comm, mul_left_comm] using hh

/-- Rescaling by the inverse of a cocycle solution makes the actual frames multiplicative. -/
theorem product_rescale_inverse (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) [IsIso (Bilinear.BilinearPullback.toHom β)]
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P)
    (r s' t' : Γ(X, ⊤)ˣ) (h : MultiplicativeFrameCoefficients.coefficient β s t v * t' = r * s') :
    Bilinear.ProductFrames.productFrame β (rescale s r⁻¹) (rescale t s'⁻¹) = rescale v t'⁻¹ := by
  apply product_rescale β s t v
  apply eq_inv_iff_mul_eq_one.mpr
  calc
    (MultiplicativeFrameCoefficients.coefficient β s t v * r⁻¹ * s'⁻¹) * t' =
        (MultiplicativeFrameCoefficients.coefficient β s t v * t') * (r⁻¹ * s'⁻¹) := by ac_rfl
    _ = (r * s') * (r⁻¹ * s'⁻¹) := congrArg (fun a => a * (r⁻¹ * s'⁻¹)) h
    _ = 1 := by rw [mul_mul_mul_comm, mul_inv_cancel, mul_inv_cancel, mul_one]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RescaledLineFrames
