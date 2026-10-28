import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.KernelTorsor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Product

/-! # Split Self Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The self-base-change of full-level multiplication is a disjoint union of copies of its source, with the first projection equal to the identity on each copy. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.fullLevelSplitSelfPullbackIso (level : A.FullLevel n) :
    (Level.Scheme.constantFullLevelScheme g n A.scheme.left).left ≅
      Limits.pullback (A.multiplication n).left (A.multiplication n).left :=
  ConstantScheme.Product.constantSchemeProductIso A.scheme (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod n))) ≪≫
    A.fullLevelKernelTorsorSchemeIso level

@[reassoc]
theorem Abelian.Schemes.AbelianScheme.fullLevelSplitSelfPullbackIso_fst (level : A.FullLevel n) :
    (A.fullLevelSplitSelfPullbackIso level).hom ≫
      pullback.fst (A.multiplication n).left (A.multiplication n).left =
        (Level.Scheme.constantFullLevelScheme g n A.scheme.left).hom := by
  change ((ConstantScheme.Product.constantSchemeProductIso A.scheme _).hom ≫ (A.fullLevelKernelTorsorSchemeIso level).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (ConstantScheme.Product.constantSchemeProductIso A.scheme _).hom ≫ k)
      (A.fullLevelKernelTorsorSchemeIso_fst level)).trans (ConstantScheme.Product.constantSchemeProductIso_fst A.scheme _))

@[reassoc]
theorem Abelian.Schemes.AbelianScheme.fullLevelSplitSelfPullbackIso_label_fst (level : A.FullLevel n)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod n))) :
    Sigma.ι (fun _ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod n)) => A.scheme.left) i ≫
      (A.fullLevelSplitSelfPullbackIso level).hom ≫
        pullback.fst (A.multiplication n).left (A.multiplication n).left = 𝟙 A.scheme.left :=
  (congrArg (fun k => Sigma.ι (fun _ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod n)) => A.scheme.left) i ≫ k)
    (A.fullLevelSplitSelfPullbackIso_fst level)).trans (ConstantScheme.Iff.constantScheme_ι_hom i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
