import OAI.AlgebraicGeometry.Comparison.Betti.PullbackUnitScalars
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

/-! # Pullback Open Scalars -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PullbackOpenScalars.RingedModules

noncomputable section

/-! Scalar transitions in an actual open frame pull back using the original
structure-sheaf map on that open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) (U : C)
  [(Over.post (X := U) F).IsContinuous (J.over U) (K.over (F.obj U))]

theorem overUnitSection_structureMap (r : S.obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (OverRingedMorphism.Modules.overStructureMap φ U).hom.app V ((SheafCohomology.Projective.Dual.SheafOfModules.overUnitSection S U r).val V) =
      (SheafCohomology.Projective.Dual.SheafOfModules.overUnitSection R (F.obj U) (φ.hom.app (op U) r)).val
        ((Over.post (X := U) F).op.obj V) :=
  ConcreteCategory.congr_hom (φ.hom.naturality V.unop.hom.op) r

variable [(SheafOfModules.pushforward.{0} (OverRingedMorphism.Modules.overStructureMap φ U)).IsRightAdjoint]

theorem pullbackOverUnitScalar (r : S.obj.obj (op U)) :
    (SheafOfModules.pullback (OverRingedMorphism.Modules.overStructureMap φ U)).map (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd S U r) ≫
        SheafOfModules.pullbackObjUnitToUnit (OverRingedMorphism.Modules.overStructureMap φ U) =
      SheafOfModules.pullbackObjUnitToUnit (OverRingedMorphism.Modules.overStructureMap φ U) ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd R (F.obj U) (φ.hom.app (op U) r) :=
  PullbackUnitScalars.RingedModules.pullbackUnitSectionEndomorphism (OverRingedMorphism.Modules.overStructureMap φ U)
    (SheafCohomology.Projective.Dual.SheafOfModules.overUnitSection S U r) (SheafCohomology.Projective.Dual.SheafOfModules.overUnitSection R (F.obj U) (φ.hom.app (op U) r))
    (overUnitSection_structureMap φ U r)

variable [HasBinaryProducts C] [HasBinaryProducts D]
  [∀ V, IsIso (prodComparison F U V)]
  [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint]

theorem modulePullbackOverUnitIso_scalar (M : SheafOfModules.{0} S)
    (e g : M.over U ≅ SheafOfModules.unit (S.over U)) (r : S.obj.obj (op U))
    (h : e.hom = g.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd S U r) :
    (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e).hom =
      (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M g).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd R (F.obj U) (φ.hom.app (op U) r) := by
  simp only [Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [h, Functor.map_comp]
  simp only [Category.assoc]
  rw [pullbackOverUnitScalar]

end

end OAI.AlgebraicGeometry.Comparison.Betti.PullbackOpenScalars.RingedModules
