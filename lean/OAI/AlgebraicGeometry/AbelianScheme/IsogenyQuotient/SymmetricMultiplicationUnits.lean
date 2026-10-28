import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricFrameDiagonal
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TransverseFrames

/-! # Symmetric Multiplication Units -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricMultiplicationUnits.Construction

noncomputable section

/-! At a fixed point, a normalized line symmetry exchanges the actual
unit frames of the fiberwise multiplication structures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

theorem multiplication_congrCoordinates_unitFrame
    {S : Scheme.{u}} {E A X : Over S} [GrpObj A]
    {p p' : E ⟶ A} {r r' : E ⟶ X} {L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left}
    (D : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication p r L) (hp : p = p') (hr : r = r')
    {T : Over S} (a : T ⟶ E) (ha : a ≫ p' = 1) :
    (Picard.PoincareBundle.MultiplicationCoordinates.congrCoordinates D hp hr).unitFrame a ha =
      D.unitFrame a ((congrArg (fun z => a ≫ z) hp).trans ha) := by
  cases hp
  cases hr
  rfl

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ A).left)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)

set_option backward.isDefEq.respectTransparency false in
theorem secondMultiplication_unitFrame_at_fixed_point
    (D : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L)
    {T : Over S} (c : T ⟶ A ⊗ A) (hh : c ≫ fst A A = 1) (hv : c ≫ snd A A = 1)
    (hfixed : c ≫ (β_ A A).hom = c)
    (hσ : (Scheme.Modules.pullback c.left).mapIso σ =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c c hfixed) :
    (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication L D σ).unitFrame c hv =
      D.unitFrame c hh := by
  change Picard.PoincareBundle.Line.FiberIsomorphisms.transportFrame (L.pullback (β_ A A).hom.left) L σ c
    ((Picard.PoincareBundle.Symmetric.MultiplicativeFrames.exchangedMultiplication L D).unitFrame c hv) = _
  rw [Picard.PoincareBundle.Symmetric.MultiplicativeFrames.exchangedMultiplication, multiplication_congrCoordinates_unitFrame]
  change (D.unitFrame (c ≫ (β_ A A).hom) _ ≪≫
      (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c (c ≫ (β_ A A).hom) rfl).symm) ≪≫
        (Scheme.Modules.pullback c.left).mapIso σ = D.unitFrame c hh
  rw [hσ]
  have hcollapse (a : T ⟶ A ⊗ A) (ha : a = c) (hca : c ≫ (β_ A A).hom = a)
      (haUnit : a ≫ fst A A = 1) :
      (D.unitFrame a haUnit ≪≫ (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c a hca).symm) ≪≫
        Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c c hfixed = D.unitFrame c hh := by
    subst a
    simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  exact hcollapse _ hfixed rfl _

set_option backward.isDefEq.respectTransparency false in
theorem returnedFirst_unitFrame_at_fixed_point
    (D : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L)
    {T : Over S} (c : T ⟶ A ⊗ A) (hh : c ≫ fst A A = 1) (hv : c ≫ snd A A = 1)
    (hfixed : c ≫ (β_ A A).hom = c)
    (hσ : (Scheme.Modules.pullback c.left).mapIso σ =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c c hfixed) :
    (Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst L D σ).unitFrame c hh = D.unitFrame c hv := by
  change Picard.PoincareBundle.Line.FiberIsomorphisms.transportFrame (L.pullback (β_ A A).hom.left) L σ c
    ((Picard.PoincareBundle.Symmetric.TransverseFrames.exchangedVertical L D).unitFrame c hh) = _
  rw [Picard.PoincareBundle.Symmetric.TransverseFrames.exchangedVertical, multiplication_congrCoordinates_unitFrame]
  change (D.unitFrame (c ≫ (β_ A A).hom) _ ≪≫
      (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c (c ≫ (β_ A A).hom) rfl).symm) ≪≫
        (Scheme.Modules.pullback c.left).mapIso σ = D.unitFrame c hv
  rw [hσ]
  have hcollapse (a : T ⟶ A ⊗ A) (ha : a = c) (hca : c ≫ (β_ A A).hom = a)
      (haUnit : a ≫ snd A A = 1) :
      (D.unitFrame a haUnit ≪≫ (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c a hca).symm) ≪≫
        Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c c hfixed = D.unitFrame c hv := by
    subst a
    simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  exact hcollapse _ hfixed rfl _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricMultiplicationUnits.Construction
