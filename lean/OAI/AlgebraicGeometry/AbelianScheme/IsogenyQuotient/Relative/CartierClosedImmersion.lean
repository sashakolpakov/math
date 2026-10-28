import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualData
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Cartier Closed Immersion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierClosedImmersion.Construction

noncomputable section

/-! The actual Cartier-Picard inclusion is a finite closed group
embedding over any base where the kernel exponent is invertible. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : X ⟶ A.scheme) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left] (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
  (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

include hn hk in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalCartierPicardInclusion_closedImmersion :
    IsClosedImmersion (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C).left := by
  let i := Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C
  have : IsFinite C.dual.X.hom := C.finite
  have : IsFinite (i.left ≫ D.abelian.scheme.hom) := i.w.symm ▸ C.finite
  have : IsFinite i.left := IsFinite.of_comp i.left D.abelian.scheme.hom
  have : Mono i := CartierMonomorphism.Construction.cartierToPicard_mono_of_invertible_kernel_exponent f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) C n hn hk
  have : Mono i.left := inferInstanceAs (Mono ((Over.forget S).map i))
  exact (IsClosedImmersion.iff_isFinite_and_mono i.left).mpr ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierClosedImmersion.Construction
