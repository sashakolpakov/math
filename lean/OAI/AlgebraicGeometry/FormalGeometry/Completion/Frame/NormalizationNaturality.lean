import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.Normalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationScalarNaturality

/-! # Normalization Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.NormalizationNaturality

noncomputable section

/-! On proper integral constant families, the unique normalized frame
commutes with arbitrary geometric base change. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

theorem properIntegralProduct_normalizedFrame_baseChange
    {K : Type u} [Field K] [IsAlgClosed K] {X Y Z T U : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π]
    (f : Y ⟶ X) (j : Z ⟶ Y) (ρ : Y ⟶ T) (τ : Z ⟶ U)
    (s : Spec (.of K) ⟶ X) (b : T ⟶ Y) (g : T ⟶ Spec (.of K))
    (c : U ⟶ Z) (t : U ⟶ T) (hb : b ≫ ρ = 𝟙 T) (hc : c ≫ τ = 𝟙 U)
    (h : c ≫ j = t ≫ b) (h₀ : b ≫ f = g ≫ s) (h₁ : c ≫ (j ≫ f) = (t ≫ g) ≫ s)
    (ho : IsPullback (j ≫ f) τ π (t ≫ g)) (M : X.Modules)
    (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K)))
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    Normalization.Construction.normalizedFrame (j ≫ f) τ c (t ≫ g) s h₁ M r (SchemeNaturality.Construction.compositeLineFrameIso f j M e) =
      SchemeNaturality.Construction.compositeLineFrameIso f j M (Normalization.Construction.normalizedFrame f ρ b g s h₀ M r e) := by
  have he : Rigidified.FrameScalar.Construction.frameAxisScalar (j ≫ f) c (t ≫ g) s h₁ M r
      (SchemeNaturality.Construction.compositeLineFrameIso f j M (Normalization.Construction.normalizedFrame f ρ b g s h₀ M r e)) = 1 :=
    (RigidificationScalarNaturality.Construction.frameAxisScalar_baseChange f j s b g c t h h₀ h₁ M r (Normalization.Construction.normalizedFrame f ρ b g s h₀ M r e)).trans
      ((congrArg t.appTop (Normalization.Construction.normalizedFrame_scalar f ρ b hb g s h₀ M r e)).trans t.appTop.hom.map_one)
  exact Proper.IntegralFrameRigidity.Construction.properIntegralProduct_normalizedFrame_unique π (j ≫ f) τ (t ≫ g) ho c hc s h₁ M r _ _
    (Normalization.Construction.normalizedFrame_scalar (j ≫ f) τ c hc (t ≫ g) s h₁ M r (SchemeNaturality.Construction.compositeLineFrameIso f j M e)) he

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.NormalizationNaturality
