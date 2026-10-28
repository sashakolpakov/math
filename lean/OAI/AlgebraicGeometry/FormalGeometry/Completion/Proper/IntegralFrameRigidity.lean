import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.AxisRigidity

/-! # Integral Frame Rigidity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.IntegralFrameRigidity

noncomputable section

/-! For a proper integral scheme over an algebraically closed field,
normalizing a frame along a section makes it unique after every base
change. Constancy of functions is derived from the native geometry. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X Y T : Scheme.{u}}
  (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π]
  (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ Spec (.of K)) (hp : IsPullback f ρ π g)
  (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T) (s : Spec (.of K) ⟶ X) (h : b ≫ f = g ≫ s)
  (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K)))

include hp hb

theorem properIntegralProduct_frameAxisScalar_injective :
    Function.Injective (Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r) := by
  have := Frame.AxisRigidity.Construction.properIntegralProduct_section_appTop_isIso π f ρ g hp b hb
  exact Frame.AxisRigidity.Construction.frameAxisScalar_injective f b g s h M r (ConcreteCategory.bijective_of_isIso b.appTop).injective

theorem properIntegralProduct_normalizedFrame_unique
    (e e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M)
    (he : Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e = 1)
    (he' : Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e' = 1) : e = e' :=
  properIntegralProduct_frameAxisScalar_injective π f ρ g hp b hb s h M r (he.trans he'.symm)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.IntegralFrameRigidity
