import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleGlobalSectionsIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Module Frame From Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleFrameFromSections

noncomputable section

/-! An actual basis of global sections of a quasicoherent module on an affine scheme constructs a genuine sheaf frame. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (M : X.Modules)

def moduleFrameSection (e : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)) : Line.Bundles.structureModule X ⟶ M :=
  (Global.Sections.moduleSectionHomEquiv M).symm (e.symm 1)

theorem moduleFrameSection_apply (e : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (r : Γ(X, ⊤)) :
    (moduleFrameSection M e).app ⊤ r = e.symm r := by
  have h : (moduleFrameSection M e).app ⊤ (1 : Γ(X, ⊤)) = e.symm 1 :=
    (Global.Sections.moduleSectionHomEquiv M).apply_symm_apply (e.symm 1)
  calc
    (moduleFrameSection M e).app ⊤ r = (moduleFrameSection M e).app ⊤ (r • (1 : Γ(X, ⊤))) := by
      rw [smul_eq_mul, mul_one]
    _ = r • (moduleFrameSection M e).app ⊤ (1 : Γ(X, ⊤)) :=
      (moduleFrameSection M e).app_smul r (1 : Γ(X, ⊤))
    _ = r • e.symm 1 := congrArg (fun z : Γ(M, ⊤) => r • z) h
    _ = e.symm r := (e.symm.map_smul r 1).symm.trans (congrArg e.symm (mul_one r))

def affineModuleFrameFromSections [IsAffine X] [M.IsQuasicoherent]
    (e : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)) : M ≅ Line.Bundles.structureModule X := by
  let φ := moduleFrameSection M e
  have : (Line.Bundles.structureModule X).IsQuasicoherent := (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  have hΓ : IsIso (φ.val.app (.op (⊤ : X.Opens))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (fun r : Γ(X, ⊤) => φ.app ⊤ r)
    have h : (fun r : Γ(X, ⊤) => φ.app ⊤ r) = e.symm := funext (moduleFrameSection_apply M e)
    rw [h]
    exact e.symm.bijective
  have := ModuleGlobalSectionsIsomorphism.affineModule_isIso_of_globalSections_isIso φ hΓ
  exact (asIso φ).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleFrameFromSections
