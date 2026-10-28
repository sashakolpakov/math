import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.ScalarRescaling
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.IntegralFrameRigidity

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.Normalization

noncomputable section

/-! A frame can be normalized along a rigidified section by an explicit
unit from the base. On a proper integral constant family this normalized
frame is unique, including after nonreduced base changes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

theorem section_appTop_left_inverse {Y T : Scheme.{u}} (ρ : Y ⟶ T) (b : T ⟶ Y)
    (hb : b ≫ ρ = 𝟙 T) (x : Γ(T, ⊤)) : b.appTop (ρ.appTop x) = x :=
  congrArg (fun a : T ⟶ T => a.appTop x) hb

def normalizedFrame {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (ρ : Y ⟶ T) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M :=
  ScalarRescaling.Construction.scalarUnitIso Y (Units.map ρ.appTop.hom.toMonoidHom
    ((Rigidified.FrameScalar.Construction.frameAxisScalar_isUnit f b g s h M r e).unit)⁻¹) ≪≫ e

theorem normalizedFrame_scalar {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (ρ : Y ⟶ T) (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T)
    (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r (normalizedFrame f ρ b g s h M r e) = 1 := by
  let u := (Rigidified.FrameScalar.Construction.frameAxisScalar_isUnit f b g s h M r e).unit
  have hu : u.val = Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e := (Rigidified.FrameScalar.Construction.frameAxisScalar_isUnit f b g s h M r e).unit_spec
  rw [normalizedFrame, ScalarRescaling.Construction.frameAxisScalar_precompIso, ScalarRescaling.Construction.scalarUnitIso_value]
  change b.appTop (ρ.appTop u.inv) * Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e = 1
  rw [section_appTop_left_inverse ρ b hb, ← hu]
  exact u.inv_val

theorem properIntegralProduct_existsUnique_normalizedFrame
    {K : Type u} [Field K] [IsAlgClosed K] {X Y T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π]
    (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ Spec (.of K)) (hp : IsPullback f ρ π g)
    (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T) (s : Spec (.of K) ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K)))
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    ∃! e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M, Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e' = 1 := by
  refine ⟨normalizedFrame f ρ b g s h M r e, normalizedFrame_scalar f ρ b hb g s h M r e, ?_⟩
  intro e' he'
  exact Proper.IntegralFrameRigidity.Construction.properIntegralProduct_normalizedFrame_unique π f ρ g hp b hb s h M r e' _ he'
    (normalizedFrame_scalar f ρ b hb g s h M r e)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.Normalization
