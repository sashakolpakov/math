import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCokernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Preimage
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Isogeny

/-! # Tate Kernel Lattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateKernelLattice.Construction

noncomputable section

/-!
The quotient of the actual target Tate preimage lattice by the source
integral Tate image is canonically the kernel of the original isogeny.
The ambient map is the rational Tate map induced by that isogeny, not an
independently supplied comparison of lattice and kernel types.
-/

open scoped TensorProduct

universe u

variable (q : ℕ) [Fact q.Prime]

def tateIntegralEmbedding (A : Type u) [AddCommGroup A] :
    TateComparison.Add.Tate.Module (H := A) q →ₗ[ℤ_[q]] TateComparison.Isogeny.Tate.RationalModule q A :=
  TensorProduct.mk ℤ_[q] ℚ_[q] (TateComparison.Add.Tate.Module (H := A) q) 1

def tateIntegralImage (A : Type u) [AddCommGroup A] : Submodule ℤ_[q] (TateComparison.Isogeny.Tate.RationalModule q A) :=
  (tateIntegralEmbedding q A).range

def tateTargetPreimage {A B : Type u} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    Submodule ℤ_[q] (TateComparison.Isogeny.Tate.RationalModule q A) :=
  (tateIntegralImage q B).comap ((TateComparison.Isogeny.Tate.rationalMap q f).restrictScalars ℤ_[q])

theorem tateIntegralEmbedding_natural {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (x : TateComparison.Add.Tate.Module (H := A) q) :
    TateComparison.Isogeny.Tate.rationalMap q f (tateIntegralEmbedding q A x) =
      tateIntegralEmbedding q B (TateComparison.Add.Tate.map q f x) := by
  simp [TateComparison.Isogeny.Tate.rationalMap, tateIntegralEmbedding]

set_option backward.isDefEq.respectTransparency false in
/-- The lattice quotient attached to the actual rational Tate isogeny
is its original kernel, by the constructed evaluation connecting map. -/
def tateTargetPreimageQuotientEquiv {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (h : ℕ) (f : A →+ B) (g : B →+ A)
    (hfg : ∀ y, f (g y) = (q ^ h) • y) (hgf : ∀ x, g (f x) = (q ^ h) • x)
    (hf : Function.Surjective f) [Finite f.ker] (hdiv : ∀ x : A, ∃ y, q • y = x) :
    tateTargetPreimage q f ⧸
      ((tateIntegralImage q A).comap (tateTargetPreimage q f).subtype).toAddSubgroup ≃+ f.ker := by
  let iA := (tateIntegralEmbedding q A).toAddMonoidHom
  let iB := (tateIntegralEmbedding q B).toAddMonoidHom
  let F := (TateComparison.Isogeny.Tate.rationalEquivOfFiniteKernel q f hf).toAddEquiv
  have hiB : Function.Injective iB := TateComparison.Isogeny.Tate.integralEmbedding_injective q
  have hnatural (a : TateComparison.Add.Tate.Module (H := A) q) : F (iA a) = iB (TateComparison.Add.Tate.map q f a) :=
    tateIntegralEmbedding_natural q f a
  exact Preimage.Construction.preimageRangeQuotientEquiv iA iB hiB (TateComparison.Add.Tate.map q f).toAddMonoidHom F hnatural
    (TateCokernel.Construction.tateConnectingMap q h f g hfg) (TateCokernel.Construction.tateConnectingMap_ker q h f g hfg hgf)
    (TateCokernel.Construction.tateConnectingMap_surjective q h f g hfg hgf hf hdiv)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateKernelLattice.Construction
