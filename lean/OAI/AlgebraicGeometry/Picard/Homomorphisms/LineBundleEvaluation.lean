import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundlePairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Line Bundle Evaluation -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleEvaluation

noncomputable section

/-! The evaluation pairing exhibits the dual line bundle as a tensor inverse. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)

theorem lineBundleEvaluation_bilinear :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (LineBundleDual.Construction.lineBundleDual L).sheaf L.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
        (LineBundleDual.Construction.lineBundleEvaluation L) =
      TensorHom.Construction.sheafBilinearUncurry (𝟙 (LineBundleDual.Construction.lineBundleDual L).sheaf) :=
  Equiv.apply_symm_apply _ _

instance lineBundleEvaluation_epi : Epi (LineBundleDual.Construction.lineBundleEvaluation L) where
  left_cancellation {P} f g h := by
    have hb := congrArg (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (LineBundleDual.Construction.lineBundleDual L).sheaf L.sheaf P) h
    rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
      lineBundleEvaluation_bilinear] at hb
    have he (U : X.Opens) (a : Γ((LineBundleDual.Construction.lineBundleDual L).sheaf, U)) (s : Γ(L.sheaf, U)) :
        f.app U (TensorHom.Construction.internalHomEval L.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U a s) =
          g.app U (TensorHom.Construction.internalHomEval L.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U a s) :=
      congrArg (fun b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (LineBundleDual.Construction.lineBundleDual L).sheaf L.sheaf P => b.app U a s) hb
    apply (SheafOfModules.unitHomEquiv P).injective
    apply Subtype.ext
    funext U
    change f.app U.unop (1 : Γ(X, U.unop)) = g.app U.unop (1 : Γ(X, U.unop))
    apply P.isSheaf.section_ext
    intro x hx
    obtain ⟨V, hVU, hxV, a, s, has⟩ := LineBundlePairing.Construction.lineBundle_dual_sections_locally L U.unop x hx
    refine ⟨V, hVU, hxV, ?_⟩
    have hf := ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE hVU).op)
      (1 : Γ(X, U.unop))
    have hg := ConcreteCategory.congr_hom (g.mapPresheaf.naturality (homOfLE hVU).op)
      (1 : Γ(X, U.unop))
    have h1 : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).presheaf.map (homOfLE hVU).op (1 : Γ(X, U.unop)) =
        (1 : Γ(X, V)) := (X.presheaf.map (homOfLE hVU).op).hom.map_one
    have hm := he V a s
    rw [has] at hm
    change f.app V ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).presheaf.map (homOfLE hVU).op (1 : Γ(X, U.unop))) =
      P.presheaf.map (homOfLE hVU).op (f.app U.unop (1 : Γ(X, U.unop))) at hf
    change g.app V ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).presheaf.map (homOfLE hVU).op (1 : Γ(X, U.unop))) =
      P.presheaf.map (homOfLE hVU).op (g.app U.unop (1 : Γ(X, U.unop))) at hg
    rw [h1] at hf hg
    exact hf.symm.trans (hm.trans hg)

instance lineBundleEvaluation_isIso : IsIso (LineBundleDual.Construction.lineBundleEvaluation L) := by
  let e : ((LineBundleDual.Construction.lineBundleDual L).tensor L).sheaf ⟶ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X).sheaf :=
    LineBundleDual.Construction.lineBundleEvaluation L
  have : Epi e := lineBundleEvaluation_epi L
  exact LineBundleEpi.Construction.lineBundle_epi_isIso ((LineBundleDual.Construction.lineBundleDual L).tensor L) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) e

/-- The canonical evaluation is an actual isomorphism of module sheaves. -/
def lineBundleEvaluationIso : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (LineBundleDual.Construction.lineBundleDual L).sheaf L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  asIso (LineBundleDual.Construction.lineBundleEvaluation L)

theorem tensorClass_dual (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass (LineBundleDual.Construction.dualLineBundleClass q) q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X := by
  induction q using Quotient.inductionOn with
  | h L => exact Quotient.sound ⟨lineBundleEvaluationIso L⟩

theorem tensorClass_dual_right (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass q (LineBundleDual.Construction.dualLineBundleClass q) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass_comm _ _).trans (tensorClass_dual q)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleEvaluation
