import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.SectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexMap

/-! # Complex Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction

noncomputable section

/-! Canonical section maps of complexes respect the actual geometric presheaf restriction maps. -/

open _root_.CategoryTheory

universe u v z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{u} R, F.op.HasPointwiseRightKanExtension P]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  [HasExt.{max u z} (Sheaf K (ModuleCat.{u} R))]
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (N : CochainComplex (Sheaf K (ModuleCat.{u} R)) ℕ)
  (a : ((constantSheaf K (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj M ⟶ N)

def constantIso : (constantSheaf K (ModuleCat.{u} R)) ⋙
    F.sheafPushforwardContinuous (ModuleCat.{u} R) J K ≅ constantSheaf J (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun L => SectionRestriction.constantIso F R J K L) (by
    intro L L' φ
    exact ((F.pushforwardContinuousSheafificationCompatibility (ModuleCat.{u} R) J K).symm.hom.naturality
      ((Functor.const Dᵒᵖ).map φ)))

def pulled : ((constantSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj M ⟶
    (((F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).mapHomologicalComplex (.up ℕ)).obj N) :=
  ((NatIso.mapHomologicalComplex (constantIso F R J K) (.up ℕ)).app M).inv ≫
    ((F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).mapHomologicalComplex (.up ℕ)).map a

def sectionMap : ComplexMap.source.{u, z} R M ⟶
    IntegralComparison.Sheaf.PresheafSectionComplex.complex.{u, v, u, z} R K N :=
  ComplexMap.map R K M N a ≫ (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R K N).hom

theorem naturality : sectionMap R K M N a ≫ IntegralComparison.Sheaf.PresheafSectionRestriction.complexMap F R J K N =
    ComplexMap.map R J M _ (pulled F R J K M N a) ≫
      (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R J _).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact (SectionRestriction.coordinates F R J K (M.X n) (N.X n) (a.f n) x.down U r).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction
