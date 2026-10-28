import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrame
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.IntegralLineBundleSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleProjectionFormula
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections

/-! # Tensor Section Restriction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction

noncomputable section

/-! Normalized sections of a twisted finite pushforward are detected on an affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections

universe u

theorem module_section_restriction_injective_of_iso
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    {U V : X.Opens} (h : V ≤ U)
    (hN : Function.Injective (N.presheaf.map (homOfLE h).op)) :
    Function.Injective (M.presheaf.map (homOfLE h).op) := by
  have : IsIso (e.hom.app U) := TensorSectionFrame.Construction.moduleMap_app_isIso_of_pullback e.hom U
  intro s t hst
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app U)).injective
  apply hN
  change N.val.map (homOfLE h).op (e.hom.val.app (.op U) s) =
    N.val.map (homOfLE h).op (e.hom.val.app (.op U) t)
  rw [← PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op s,
    ← PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op t]
  exact congrArg (e.hom.app V) hst

theorem pushforward_lineBundle_section_restriction_injective
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
    (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M)
    {U V : Y.Opens} (h : V ≤ U) [Nonempty (f ⁻¹ᵁ V)] :
    Function.Injective (((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE h).op) := by
  exact IntegralLineBundleSections.Construction.lineBundle_section_restriction_injective M hM (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)

local instance tensorSectionRestrictionMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem tensorPushforward_lineBundle_section_restriction_injective
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
    (P : Y.Modules) (hP : LineBundle.Construction.IsLineBundle P)
    {U V : Y.Opens} (h : V ≤ U) [Nonempty (f ⁻¹ᵁ V)] :
    Function.Injective ((((Scheme.Modules.pushforward f).obj (LineBundle.Construction.structureSheafModule X)) ⊗ P).presheaf.map
      (homOfLE h).op) := by
  let L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y := ⟨P, hP⟩
  let N := (Scheme.Modules.pushforward f).obj (LineBundle.Construction.structureSheafModule X)
  let M := SheafTensor.Construction.sheafTensor (LineBundle.Construction.structureSheafModule X) ((Scheme.Modules.pullback f).obj P)
  let e : N ⊗ P ≅ (Scheme.Modules.pushforward f).obj M :=
    AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso N P ≪≫ LineBundleProjectionFormula.Construction.lineBundleProjectionFormula f L (LineBundle.Construction.structureSheafModule X)
  apply module_section_restriction_injective_of_iso e h
  exact pushforward_lineBundle_section_restriction_injective f M
    (TensorRestriction.Construction.isLineBundle_sheafTensor (LineBundle.Construction.isLineBundle_structureSheaf X) (LineBundle.Construction.isLineBundle_pullback f P hP)) h

def tensorSectionGlobalCoefficient {X : Scheme.{u}} (M : X.Modules) {P : X.Modules}
    (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)] (s : Γ(M ⊗ P, ⊤)) : Γ(M, U) :=
  (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv M a U).symm
    ((M ⊗ P).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)

theorem tensorSectionGlobalCoefficient_injective
    {X : Scheme.{u}} (M : X.Modules) {P : X.Modules}
    (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)]
    (h : Function.Injective ((M ⊗ P).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) :
    Function.Injective (tensorSectionGlobalCoefficient M a U) :=
  (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv M a U).symm.injective.comp h

theorem tensorSectionGlobalCoefficient_naturality
    {X : Scheme.{u}} {M N P : X.Modules} (q : M ⟶ N)
    (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)] (s : Γ(M ⊗ P, ⊤)) :
    tensorSectionGlobalCoefficient N a U ((q ⊗ₘ 𝟙 P).app ⊤ s) =
      q.app U (tensorSectionGlobalCoefficient M a U s) := by
  unfold tensorSectionGlobalCoefficient
  change (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv N a U).symm
      ((N ⊗ P).val.map (homOfLE (le_top : U ≤ ⊤)).op
        ((q ⊗ₘ 𝟙 P).val.app (.op ⊤) s)) = _
  rw [← PresheafOfModules.naturality_apply (q ⊗ₘ 𝟙 P).val
    (homOfLE (le_top : U ≤ ⊤)).op s]
  exact TensorSectionFrame.Construction.tensorSectionFrameAppEquiv_naturality q a U _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction
