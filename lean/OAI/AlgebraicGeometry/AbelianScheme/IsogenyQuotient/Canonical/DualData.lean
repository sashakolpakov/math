import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierMonomorphism

/-! # Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualData.Construction

noncomputable section

/-! Retain the original Picard representative and Poincare bundle with
its canonical tensor-product group law. This construction requires no
comparison with the originally supplied group law over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def canonicalDualAbelianData : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A :=
  (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.toBundled A D.abelian.smoothDimension

theorem canonicalDualAbelianData_scheme : (canonicalDualAbelianData D).abelian.scheme = D.abelian.scheme := rfl

theorem canonicalDualAbelianData_poincare : (canonicalDualAbelianData D).poincare = D.poincare := rfl

variable {X : Over S} [GrpObj X] (f : X ⟶ A.scheme) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

def canonicalCartierPicardInclusion : C.dual.X ⟶ (canonicalDualAbelianData D).abelian.scheme :=
  CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) C

set_option backward.isDefEq.respectTransparency false in
instance canonicalCartierPicardInclusion_isMonHom : IsMonHom (canonicalCartierPicardInclusion D f C) :=
  CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_isMonHom f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) C

set_option backward.isDefEq.respectTransparency false in
theorem canonicalCartierPicardInclusion_pow (n : ℕ)
    (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    canonicalCartierPicardInclusion D f C ^ n = 1 :=
  CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicard_pow f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) n hk C

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualData.Construction
