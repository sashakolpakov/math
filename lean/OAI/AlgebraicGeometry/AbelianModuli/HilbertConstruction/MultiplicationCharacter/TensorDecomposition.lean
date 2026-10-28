import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ProjectionFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.LineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorFiniteBiproducts

/-! # Tensor Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The direct image of a pulled-back line bundle splits into its actual twists by the multiplication-character line bundles. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterTensorDecomposition (L : Line.Bundles.LineBundle A.scheme.left)
    (hN : (N : K) ≠ 0) :
    (Scheme.Modules.pushforward (A.multiplication N).left).obj
      (L.pullback (A.multiplication N).left).sheaf ≅
      ⨁ (fun χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ =>
        (L.tensor (A.multiplicationCharacterLineBundle level χ hN)).sheaf) := by
  classical
  letI : Fintype (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) := Fintype.ofFinite _
  let M := fun χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ =>
    A.multiplicationCharacterSheaf level χ
  let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor
  letI : F.Additive := CategoryTheory.Functor.additive_of_preserves_binary_products F
  letI : PreservesBiproduct M F := HilbertConstruction.Additive.FunctorFiniteBiproducts.additive_functor_preserves_finite_biproduct F M
  exact (LineBundle.ProjectionFormula.lineBundlePushforwardPullbackIso (A.multiplication N).left L).symm ≪≫
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence_objIso L (A.multiplicationStructurePushforward N)).symm ≪≫
    F.mapIso (A.multiplicationCharacterDecomposition level hN) ≪≫
    F.mapBiproduct M ≪≫
    biproduct.mapIso (fun χ => LineBundle.TensorEquivalence.lineBundleTensorEquivalence_objIso L (M χ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
