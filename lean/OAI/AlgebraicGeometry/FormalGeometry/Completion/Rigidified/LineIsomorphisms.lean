import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.AxisRigidity
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidificationAt

/-! # Line Isomorphisms -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.LineIsomorphisms.Construction

noncomputable section

/-! Actual line isomorphisms have unique prescribed restrictions along
a section of a proper integral constant family, for arbitrary bases. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem properConstantFamily_existsUnique_lineIso
    {K : Type u} [Field K] [IsAlgClosed K] {X Y T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π]
    (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ Spec (.of K)) (hp : IsPullback f ρ π g)
    (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T)
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : L.sheaf ≅ M.sheaf)
    (φ : (L.pullback b).sheaf ≅ (M.pullback b).sheaf) :
    ∃! e' : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback b).mapIso e' = φ := by
  have := Frame.AxisRigidity.Construction.properIntegralProduct_section_appTop_isIso π f ρ g hp b hb
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso b L M e φ

theorem properConstantFamily_lineIso_unique
    {K : Type u} [Field K] [IsAlgClosed K] {X Y T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π]
    (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ Spec (.of K)) (hp : IsPullback f ρ π g)
    (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T)
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e e' : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback b).mapIso e = (Scheme.Modules.pullback b).mapIso e') : e = e' := by
  have := Frame.AxisRigidity.Construction.properIntegralProduct_section_appTop_isIso π f ρ g hp b hb
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.iso_unique b L M e e' h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.LineIsomorphisms.Construction
