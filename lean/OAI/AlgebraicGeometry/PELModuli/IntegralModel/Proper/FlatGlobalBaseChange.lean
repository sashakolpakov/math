import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatCech
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SectionBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatScalarExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Flat Global Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatGlobalBaseChange

noncomputable section

/-! Flat coefficient base change gives a surjective actual section map,
with its canonical formula on pure tensors, for proper flat families. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

theorem properFlat_exists_surjective_section_map_of_flat
    {X Y S T : Scheme.{0}} [IsAffine S] [IsAffine T] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (a : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback a ρ f g)
    (hg : g.appTop.hom.Flat) :
    ∃ b : (ModuleCat.extendScalars g.appTop.hom).obj
        ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤)) ⟶
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback a).obj L.sheaf)).obj (op ⊤),
      Function.Surjective b ∧
      ∀ s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤),
        b ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
          CechPullbackSectionNormalization.pullbackTopSection a L.sheaf s := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  obtain ⟨k, U, ha, _, hcover⟩ := L.exists_finite_affine_frames
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr (hcover y)
  obtain ⟨D, φ, hφ, _, _, _, hbase⟩ :=
    FlatCech.properFlat_exists_affine_baseChange_model f L U hU ha
  have := hφ
  have : QuasiIso (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a f ρ g hp.w L.sheaf U φ) :=
    hbase _ _ a ρ g hp
  let b := SectionBaseChange.modelSectionsBaseChangeMap a f ρ g hp.w L.sheaf U hU φ
  have hk : (D.d 0 1).hom.shortComplexKer.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      (fun _ => by simp [LinearMap.shortComplexKer])
  exact ⟨b, SectionBaseChange.modelSectionsBaseChangeMap_surjective _ _ _ _ _ _ _ _ _
    (FlatScalarExactness.native_scalar_exact_of_flat g.appTop.hom hg _ hk),
    SectionBaseChange.modelSectionsBaseChangeMap_one _ _ _ _ _ _ _ _ _⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatGlobalBaseChange
