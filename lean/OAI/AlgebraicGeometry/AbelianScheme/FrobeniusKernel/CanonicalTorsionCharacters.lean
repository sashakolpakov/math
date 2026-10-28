import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalDualTorsionFunctor
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierRepresentativeCharacters
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange

/-! # Canonical Torsion Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalTorsionCharacters.Construction

noncomputable section

/-! The canonical character-line construction gives the original
CMPoints ambient torsion-character isomorphism on a geometric source.
This is constructed from the source polarization and CartierDuality's proved
duality, without assuming a torsion pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (n : ℕ) (hn : 0 < n)
variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
  (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ n))))

def canonicalTorsionCartierPointIso : yonedaGrp.obj C.dual ≅ A.dual.abelian.torsionFunctor n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
  have : IsCommMonObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
    Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
  exact yonedaGrp.mapIso (CanonicalTorsionCartierIso.Construction.canonicalTorsionCartierIso A n hn C) ≪≫ CanonicalDualTorsionFunctor.Construction.canonicalDualTorsionYonedaIso A n

def canonicalTorsionCharacterIso : PELModuli.CMPoints.DualityPairing.TorsionCharacterIso A n :=
  Functor.isoWhiskerRight (canonicalTorsionCartierPointIso A n hn C).symm
      (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≪≫
    CartierRepresentativeCharacters.Construction.cartierRepresentativeCharacterIso C ≪≫
    CartierDuality.CharacterBaseChange.Construction.Slices.presheafHomCongr (IntrinsicTorsionFunctor.Construction.multiplicationKernelYonedaIso A.abelian n) (Iso.refl _)

theorem canonicalTorsionCharacterIso_apply (T : Over (Spec (.of k)))
    (y : (A.dual.abelian.torsionFunctor n).obj (.op T))
    (U : Over T) (x : (A.abelian.torsionFunctor n).obj (.op U.left)) :
    (((canonicalTorsionCharacterIso A n hn C).hom.app (.op T) (ULift.up y)).app (.op U)) x =
      ((C.sectionEquiv T ((canonicalTorsionCartierPointIso A n hn C).inv.app (.op T) y)).app (.op U))
        ((IntrinsicTorsionFunctor.Construction.multiplicationKernelYonedaIso A.abelian n).inv.app (.op U.left) x) := rfl

theorem canonicalTorsionCharacterIso_additive :
    PELModuli.CMPoints.DualityPairing.TorsionCharacterAdditive A n (canonicalTorsionCharacterIso A n hn C) := by
  intro T y z U x
  let d := (canonicalTorsionCartierPointIso A n hn C).inv.app (.op T)
  let x₀ := (IntrinsicTorsionFunctor.Construction.multiplicationKernelYonedaIso A.abelian n).inv.app (.op U.left) x
  let v (w : T ⟶ C.dual.X) := ((C.sectionEquiv T w).app (.op U)) x₀
  have hm : v (d y * d z) = v (d y) * v (d z) :=
    congrArg (fun c => (c.app (.op U)) x₀) ((C.sectionEquiv T).map_mul (d y) (d z))
  change v (d (y * z)) = v (d y) * v (d z)
  exact (congrArg v (d.hom.map_mul y z)).trans hm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalTorsionCharacters.Construction
