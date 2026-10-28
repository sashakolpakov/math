import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ConcreteKernelPairing

/-! # Symmetric Frame Diagonal -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricFrameDiagonal.Construction

noncomputable section

/-!
Diagonal normalization of a genuine line symmetry is preserved on every
test scheme. The resulting second kernel frame agrees with the first
frame at a diagonal point, giving trivial diagonal values of the actual
frame-ratio pairing.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

theorem fixedLineSymmetry_at_point
    {S : Scheme.{u}} {E K T : Over S} (p : E ⟶ E) (q : K ⟶ E) (hq : q ≫ p = q)
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
    (σ : (Scheme.Modules.pullback p.left).obj L.sheaf ≅ L.sheaf)
    (hnorm : (Scheme.Modules.pullback q.left).mapIso σ = Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison p L q q hq)
    (g : T ⟶ K) (c : T ⟶ E) (hc : g ≫ q = c) (hfixed : c ≫ p = c) :
    (Scheme.Modules.pullback c.left).mapIso σ = Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison p L c c hfixed := by
  have h₁ := Picard.PoincareBundle.GlobalFrameNaturality.comparison_pullback p L g q q hq c c hfixed hc hc
  have h₂ := Picard.PoincareBundle.Line.FiberIsomorphisms.fiberIso_pullback (L.pullback p.left) L σ g q c hc
  change (Scheme.Modules.pullback g.left).mapIso ((Scheme.Modules.pullback q.left).mapIso σ) ≪≫
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L g q c hc =
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (L.pullback p.left) g q c hc ≪≫ (Scheme.Modules.pullback c.left).mapIso σ at h₂
  rw [hnorm] at h₂
  apply Iso.ext
  apply (cancel_epi (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (L.pullback p.left) g q c hc).hom).mp
  exact congrArg Iso.hom (h₂.symm.trans h₁)

theorem kernelFrames_congrCoordinates_frame
    {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [GrpObj B]
    {p p' : E ⟶ A} {r r' : E ⟶ X} (f : A ⟶ B) [IsMonHom f]
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (D : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication p r L)
    (F : Picard.PoincareBundle.FiberwiseMultiplication.KernelFrames p r L f D) (hp : p = p') (hr : r = r')
    {T : Over S} (k : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (a : T ⟶ E)
    (ha : k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ p') :
    (Picard.PoincareBundle.Kernel.FramesPullback.congrCoordinates f L D F hp hr).frame k a ha =
      F.frame k a (ha.trans (congrArg (fun z => a ≫ z) hp).symm) := by
  cases hp
  cases hr
  rfl

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ A).left)
  (D : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)
  (f : A ⟶ B) [IsMonHom f] (F : Picard.PoincareBundle.FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f D)

set_option backward.isDefEq.respectTransparency false in
theorem secondKernelFrame_eq_at_fixed_point
    {T : Over S} (k : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (c : T ⟶ A ⊗ A)
    (hk : k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = c ≫ fst A A)
    (hl : k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = c ≫ snd A A)
    (hfixed : c ≫ (β_ A A).hom = c)
    (hσ : (Scheme.Modules.pullback c.left).mapIso σ =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c c hfixed) :
    (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames L D σ f F).frame k c hl = F.frame k c hk := by
  change Picard.PoincareBundle.Line.FiberIsomorphisms.transportFrame (L.pullback (β_ A A).hom.left) L σ c
    ((Picard.PoincareBundle.Symmetric.MultiplicativeFrames.exchangedFrames L D f F).frame k c hl) = _
  rw [Picard.PoincareBundle.Symmetric.MultiplicativeFrames.exchangedFrames, kernelFrames_congrCoordinates_frame]
  change (F.frame k (c ≫ (β_ A A).hom) _ ≪≫
      (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c (c ≫ (β_ A A).hom) rfl).symm) ≪≫
        (Scheme.Modules.pullback c.left).mapIso σ = F.frame k c hk
  rw [hσ]
  have hcollapse (a : T ⟶ A ⊗ A) (ha : a = c) (hca : c ≫ (β_ A A).hom = a)
      (hk' : k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ fst A A) :
      (F.frame k a hk' ≪≫ (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c a hca).symm) ≪≫
        Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L c c hfixed = F.frame k c hk := by
    subst a
    simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  exact hcollapse _ hfixed rfl _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricFrameDiagonal.Construction
