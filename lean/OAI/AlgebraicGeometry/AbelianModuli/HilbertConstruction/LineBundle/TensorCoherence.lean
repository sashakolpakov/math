import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorLocalFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceNeighborhoods
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType

/-! # Tensor Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorCoherence

noncomputable section

/-! The actual tensor product with a line bundle preserves quasicoherence and finite type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem tensorModuleRight_lineBundle_quasicoherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (L : Line.Bundles.LineBundle X) :
    (Tensor.ProductSheaf.tensorModule M L.sheaf).IsQuasicoherent := by
  apply HilbertConstruction.Module.QuasicoherenceNeighborhoods.module_quasicoherent_of_affine_neighborhoods
  intro x
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := L.exists_affine_frame x
  refine ⟨U, hx, hU, ?_⟩
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    (TensorLocalFrames.tensorModuleRightFrameIso U.ι M L e).symm inferInstance

theorem tensorModuleRight_lineBundle_finiteType {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (L : Line.Bundles.LineBundle X) :
    (Tensor.ProductSheaf.tensorModule M L.sheaf).IsFiniteType := by
  have : (Tensor.ProductSheaf.tensorModule M L.sheaf).IsQuasicoherent := tensorModuleRight_lineBundle_quasicoherent M L
  apply HilbertConstruction.Finite.FromAffineSectionNeighborhoods.module_finiteType_of_affine_section_neighborhoods
  intro x
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := L.exists_affine_frame x
  have : IsAffine U.toScheme := hU
  have : (M.restrict U.ι).IsFiniteType := Quasicoherent.RestrictionFiniteType.quasicoherent_openRestrict_finiteType U.ι M
  have : Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) :=
    Affine.QuasicoherentFiniteTypeSections.affine_quasicoherent_finiteType_sections_finite (M.restrict U.ι)
  let F : U.toScheme.Modules ⥤ ModuleCat.{u} Γ(U.toScheme, ⊤) :=
    SheafOfModules.evaluation U.toScheme.ringCatSheaf (.op ⊤)
  let E : Γ(M.restrict U.ι, ⊤) ≃ₗ[Γ(U.toScheme, ⊤)]
      Γ((Tensor.ProductSheaf.tensorModule M L.sheaf).restrict U.ι, ⊤) :=
    (F.mapIso (TensorLocalFrames.tensorModuleRightFrameIso U.ι M L e).symm).toLinearEquiv
  exact ⟨U, hx, hU, Module.Finite.equiv E⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorCoherence
