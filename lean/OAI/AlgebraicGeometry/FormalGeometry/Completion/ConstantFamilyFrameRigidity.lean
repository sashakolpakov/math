import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.NormalizationNaturality

/-! # Constant Family Frame Rigidity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantFamilyFrameRigidity

noncomputable section

/-! Frame rigidity only needs the total family to be a base change of
a proper integral scheme. The line bundle may vary with the parameter
and may be pulled back from an unrelated ambient family. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {A X Y S T : Scheme.{u}}
  (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
  (p : Y ⟶ A) (ρ : Y ⟶ T) (t : T ⟶ Spec (.of K)) (hp : IsPullback p ρ a t)
  (f : Y ⟶ X) (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T)
  (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
  (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

include hp hb

theorem properConstantFamily_frameAxisScalar_injective :
    Function.Injective (Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r) := by
  have := Frame.AxisRigidity.Construction.properIntegralProduct_section_appTop_isIso a p ρ t hp b hb
  exact Frame.AxisRigidity.Construction.frameAxisScalar_injective f b g s h M r (ConcreteCategory.bijective_of_isIso b.appTop).injective

theorem properConstantFamily_normalizedFrame_unique
    (e e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M)
    (he : Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e = 1)
    (he' : Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e' = 1) : e = e' :=
  properConstantFamily_frameAxisScalar_injective a p ρ t hp f b hb g s h M r (he.trans he'.symm)

theorem properConstantFamily_existsUnique_normalizedFrame
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    ∃! e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M, Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e' = 1 := by
  refine ⟨Frame.Normalization.Construction.normalizedFrame f ρ b g s h M r e, Frame.Normalization.Construction.normalizedFrame_scalar f ρ b hb g s h M r e, ?_⟩
  intro e' he'
  exact properConstantFamily_normalizedFrame_unique a p ρ t hp f b hb g s h M r e' _ he'
    (Frame.Normalization.Construction.normalizedFrame_scalar f ρ b hb g s h M r e)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantFamilyFrameRigidity
