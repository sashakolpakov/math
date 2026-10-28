import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductIs

/-! # Axis Rigidity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.AxisRigidity

noncomputable section

/-! A frame is determined by its value on a section whenever global
functions come from the base. The required function isomorphism is
derived for proper integral constant families after arbitrary base change. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

theorem pullbackStructureEnd_injective {Y T : Scheme.{u}} (b : T ⟶ Y)
    (hb : Function.Injective b.appTop) :
    Function.Injective (fun a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) => (Scheme.Modules.pullback b).map a) := by
  intro a a' h
  apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective Y
  apply hb
  have he := congrArg (fun z => AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T
    ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).inv ≫ z ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).hom)) h
  rw [Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback, Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback] at he
  exact he

theorem pullbackFrameIso_injective {Y T : Scheme.{u}} (b : T ⟶ Y)
    (hb : Function.Injective b.appTop) {M : Y.Modules}
    (e e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ M)
    (h : (Scheme.Modules.pullback b).map e.hom = (Scheme.Modules.pullback b).map e'.hom) : e = e' := by
  have he : (Scheme.Modules.pullback b).map (e.hom ≫ e'.inv) =
      (Scheme.Modules.pullback b).map (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) := by
    rw [Functor.map_comp, h, ← Functor.map_comp, e'.hom_inv_id]
  have hi := pullbackStructureEnd_injective b hb he
  apply Iso.ext
  calc
    e.hom = (e.hom ≫ e'.inv) ≫ e'.hom := by rw [Category.assoc, e'.inv_hom_id, Category.comp_id]
    _ = e'.hom := by rw [hi, Category.id_comp]

theorem frameAxisScalar_injective {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (hb : Function.Injective b.appTop) :
    Function.Injective (Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r) := by
  intro e e' he
  have hi := AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective T he
  change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).inv ≫
      ((Scheme.Modules.pullback b).map e.hom ≫ (Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom) =
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).inv ≫
      ((Scheme.Modules.pullback b).map e'.hom ≫ (Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom) at hi
  apply pullbackFrameIso_injective b hb e e'
  exact (cancel_mono (Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom).mp
    ((cancel_epi (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).inv).mp hi)

theorem section_appTop_isIso {Y T : Scheme.{u}} (ρ : Y ⟶ T) (b : T ⟶ Y)
    (hb : b ≫ ρ = 𝟙 T) [IsIso ρ.appTop] : IsIso b.appTop := by
  have : IsIso (ρ.appTop ≫ b.appTop) := by
    rw [← Scheme.Hom.comp_appTop, hb]
    infer_instance
  exact IsIso.of_isIso_comp_left ρ.appTop b.appTop

theorem properIntegralProduct_section_appTop_isIso
    {K : Type u} [Field K] [IsAlgClosed K] {X Y T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π]
    (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ Spec (.of K)) (hp : IsPullback f ρ π g)
    (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T) : IsIso b.appTop := by
  have : IsIso ρ.appTop := Quotients.FiniteDescent.CartesianProductIs.Construction.CartesianProductFunctions.isIso_app π f ρ g hp ⊤
  exact section_appTop_isIso ρ b hb

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.AxisRigidity
