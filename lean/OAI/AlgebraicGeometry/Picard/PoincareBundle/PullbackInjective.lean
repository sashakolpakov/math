import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ComplementaryIsogeny
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.PullbackCancellation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveOverQuotient
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMapCongruence

/-! # Pullback Injective -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackInjective

noncomputable section

/-!
# Injectivity of polarization pullback on group homomorphisms

The complement is constructed from the scheme-theoretic torsion-kernel condition.
Scalar compatibility of duality is proved from the genuine Poincare products.
Cancellation uses an epimorphic scalar map on the source.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters OAI.AlgebraicGeometry.Picard.PoincareBundle.ComplementaryIsogeny

variable {S : Scheme.{u}} {A B DA DB : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj DB]
  (HA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy DA)
  (HB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy DB)
  (Q : Line.Bundles.LineBundle (DB ⊗ B).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst DB B) (snd DB B) Q)
  (Dv : FiberwiseMultiplication.Multiplication (snd DB B) (fst DB B) Q)
  (hQ : HB.homEquiv (𝟙 DB) = Product.Map.sectionClass Q (Vertical.ProductParameters.globalProduct DB B Q Dv)
    (Vertical.ProductParameters.globalProduct_isIso DB B Q Dv) (𝟙 DB))
  (f : A ⟶ B) [IsMonHom f] (n : ℕ)
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

include Q Dh Dv hQ hker

/-- The actual dual pullback is injective on homomorphisms when the scalar source map is epimorphic. -/
theorem pullback_injective [EffectiveEpi f] [Epi (f ⊗ₘ f)] [Epi ((𝟙 B) ^ n)]
    (a b : B ⟶ DB) [IsMonHom a] [IsMonHom b]
    (h : f ≫ a ≫ DualMaps.representedDualMap HA HB f = f ≫ b ≫ DualMaps.representedDualMap HA HB f) : a = b := by
  have : IsMonHom (ComplementaryIsogeny.complement f n hker) := ComplementaryIsogeny.complement_isMonHom f n hker
  have hd : DualMaps.representedDualMap HA HB f ≫ DualMaps.representedDualMap HB HA (ComplementaryIsogeny.complement f n hker) =
      (𝟙 DB) ^ n := by
    rw [← DualMaps.representedDualMap_comp]
    exact (DualMapCongruence.representedDualMap_congr HB HB _ _ (ComplementaryIsogeny.right_complement f n hker)).trans
      (Poincare.ScalarClasses.representedDualMap_scalar Q Dh Dv HB hQ n)
  exact Scalar.PullbackCancellation.pullback_injective f (DualMaps.representedDualMap HA HB f)
    (DualMaps.representedDualMap HB HA (ComplementaryIsogeny.complement f n hker)) n hd a b h

/-- Affine faithfully flat quotients supply the effective-quotient hypotheses by actual scheme descent. -/
theorem affine_pullback_injective [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    [Epi ((𝟙 B) ^ n)] (a b : B ⟶ DB) [IsMonHom a] [IsMonHom b]
    (h : f ≫ a ≫ DualMaps.representedDualMap HA HB f = f ≫ b ≫ DualMaps.representedDualMap HA HB f) : a = b := by
  have : EffectiveEpi f := EffectiveOverQuotient.affine_effective f
  have : EffectiveEpi (f ⊗ₘ f) := EffectiveOverQuotient.tensor_effective f
  exact pullback_injective HA HB Q Dh Dv hQ f n hker a b h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackInjective
