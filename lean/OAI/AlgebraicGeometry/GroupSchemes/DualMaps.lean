import OAI.AlgebraicGeometry.GroupSchemes.Verschiebung

/-! # Dual Maps -/

namespace OAI.AlgebraicGeometry.GroupSchemes.DualMaps.FiniteEtale

noncomputable section

/-!
# FiniteEtale: dual maps and naturality of Verschiebung

Precomposition by a coalgebra homomorphism is a homomorphism of convolution
algebras. This gives naturality of the constructed Verschiebung without
assuming a Dieudonné correspondence.
-/

open OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale WithConv

universe u v w

variable (k : Type u) [Field k]
variable {A : Type v} [AddCommGroup A] [Module k A] [Coalgebra k A]
  [Coalgebra.IsCocomm k A]
variable {B : Type w} [AddCommGroup B] [Module k B] [Coalgebra k B]
  [Coalgebra.IsCocomm k B]

local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convAlgebra
local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k B) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k B) := LinearMap.convAlgebra

/-- Transpose, with the convolution type synonyms retained. -/
def transposeLinear (f : A →ₗc[k] B) : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k B →ₗ[k] AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A :=
  (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateLinearEquiv k A).symm.toLinearMap ∘ₗ f.toLinearMap.dualMap ∘ₗ
    (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateLinearEquiv k B).toLinearMap

omit [Coalgebra.IsCocomm k A] [Coalgebra.IsCocomm k B] in
@[simp]
theorem transposeLinear_apply (f : A →ₗc[k] B) (φ : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k B) (x : A) :
    transposeLinear k f φ x = φ (f x) := rfl

/-- A coalgebra map transposes to a genuine algebra map. -/
def transposeAlgHom (f : A →ₗc[k] B) : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k B →ₐ[k] AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A :=
  AlgHom.ofLinearMap (transposeLinear k f)
    (by
      ext x
      change Coalgebra.counit (f x) = Coalgebra.counit (R := k) x
      exact CoalgHomClass.counit_comp_apply f x)
    (by
      intro φ ψ
      ext x
      exact congrArg (fun g : A →ₗ[k] k => g x)
        (LinearMap.convMul_comp_coalgHom_distrib φ ψ f))

omit [Coalgebra.IsCocomm k A] [Coalgebra.IsCocomm k B] in
@[simp]
theorem transposeAlgHom_apply (f : A →ₗc[k] B) (φ : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k B) (x : A) :
    transposeAlgHom k f φ x = φ (f x) := rfl

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
  [Module.Finite k A] [Module.Finite k B]

/-- The constructed Verschiebung commutes with every coalgebra homomorphism. -/
theorem verschiebung_natural (f : A →ₗc[k] B) (x : A) :
    f (Verschiebung.FiniteEtale.verschiebungFun p k A x) = Verschiebung.FiniteEtale.verschiebungFun p k B (f x) := by
  apply (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv k B).injective
  ext φ
  simp only [AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv_apply]
  calc
    φ (f (Verschiebung.FiniteEtale.verschiebungFun p k A x)) =
        transposeAlgHom k f φ (Verschiebung.FiniteEtale.verschiebungFun p k A x) := rfl
    _ = (frobeniusEquiv k p).symm ((transposeAlgHom k f φ ^ p) x) :=
      Verschiebung.FiniteEtale.eval_verschiebung p k A _ x
    _ = (frobeniusEquiv k p).symm (transposeAlgHom k f (φ ^ p) x) := by rw [map_pow]
    _ = (frobeniusEquiv k p).symm ((φ ^ p) (f x)) := rfl
    _ = φ (Verschiebung.FiniteEtale.verschiebungFun p k B (f x)) := (Verschiebung.FiniteEtale.eval_verschiebung p k B φ (f x)).symm

end

end OAI.AlgebraicGeometry.GroupSchemes.DualMaps.FiniteEtale
