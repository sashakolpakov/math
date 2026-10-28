import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PullbackKernelTorsion
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId

/-! # Pullback Kernel Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.PullbackKernelTorsion.Construction

noncomputable section

/-! The affine-parameter kernel torsion statement in the product
coordinates used by actual Picard families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

theorem productPullbackTrivialClass_torsion
    (Q : Over (Spec (.of k))) [IsAffine Q.left]
    (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (Q ⊗ B).left)
    (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 Q) ⊗ₘ f).left c = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Q ⊗ A).left)
    (n : ℕ) (hn : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    c ^ n = 1 := by
  let eA := pullbackSymmetry Q.hom A.hom
  let eB := pullbackSymmetry Q.hom B.hom
  let c' := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eB.inv c
  have hs : ((Over.pullback Q.hom).map f).left ≫ eB.inv = eA.inv ≫ ((𝟙 Q) ⊗ₘ f).left := by
    dsimp only [eA, eB]
    simp only [Over.pullback_map_left, Over.tensorHom_left, Over.id_left]
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd,
        pullbackSymmetry_inv_comp_snd_assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
  have hc' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left c' =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj A).left := by
    dsimp only [c']
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hs, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hc]
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial _
  have hp := Parameter.PullbackKernelTorsion.Construction.parameterPullbackTrivialClass_torsion f Q c' hc' n hn
  have hrec : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eB.hom c' = c := by
    dsimp only [c']
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, eB.hom_inv_id, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
  have ht := congrArg (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map eB.hom) hp
  rw [map_pow, map_one] at ht
  change (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eB.hom c') ^ n = 1 at ht
  rwa [hrec] at ht

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.PullbackKernelTorsion.Construction
