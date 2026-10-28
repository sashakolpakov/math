import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatCech
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FiberKernelBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Flat Section Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatSectionBaseChange

noncomputable section

/-! Vanishing of first cohomology on the actual fiber of a proper flat
family makes the canonical map on global sections surjective after
scalar extension. Every cover and finite projective model is constructed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

theorem properFlat_exists_surjective_fiber_section_map
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (x : S)
    [Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.pullback (f.fiberι x)).obj L.sheaf) 1)] :
    ∃ b : (ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).obj
        ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤)) ⟶
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f.fiberToSpecResidueField x)
        ((Scheme.Modules.pullback (f.fiberι x)).obj L.sheaf)).obj (op ⊤),
      Function.Surjective b ∧
      ∀ s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤),
        b ((1 : Γ(Spec (S.residueField x), ⊤)) ⊗ₜ[Γ(S, ⊤),(S.fromSpecResidueField x).appTop.hom] s) =
          CechPullbackSectionNormalization.pullbackTopSection (f.fiberι x) L.sheaf s := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  obtain ⟨k, U, ha, _, hcover⟩ := L.exists_finite_affine_frames
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr (hcover y)
  obtain ⟨D, φ, hφ, _, hfin, hproj, hbase⟩ :=
    FlatCech.properFlat_exists_affine_baseChange_model f L U hU ha
  have := hφ
  have : Module.Finite Γ(S, ⊤) (D.X 0) := hfin 0
  have : Module.Finite Γ(S, ⊤) (D.X 1) := hfin 1
  have : Module.Finite Γ(S, ⊤) (D.X 2) := hfin 2
  have : Module.Projective Γ(S, ⊤) (D.X 0) := hproj 0
  have : Module.Projective Γ(S, ⊤) (D.X 1) := hproj 1
  have : Module.Projective Γ(S, ⊤) (D.X 2) := hproj 2
  have hmodel : QuasiIso (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (f.fiberι x) f (f.fiberToSpecResidueField x)
      (S.fromSpecResidueField x) (f.fiber_fac x) L.sheaf U φ) :=
    hbase _ _ (f.fiberι x) (f.fiberToSpecResidueField x) (S.fromSpecResidueField x)
      (IsPullback.of_hasPullback f (S.fromSpecResidueField x))
  let b := SectionBaseChange.modelSectionsBaseChangeMap (f.fiberι x) f (f.fiberToSpecResidueField x)
    (S.fromSpecResidueField x) (f.fiber_fac x) L.sheaf U hU φ
  exact ⟨b, SectionBaseChange.modelSectionsBaseChangeMap_surjective _ _ _ _ _ _ _ _ _
    (FiberKernelBaseChange.actualFiber_native_kernel_baseChange_exact f L.sheaf U hU ha φ x),
    SectionBaseChange.modelSectionsBaseChangeMap_one _ _ _ _ _ _ _ _ _⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatSectionBaseChange
