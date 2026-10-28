import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.HomEquality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.ImagePairingTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierIsoPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSelfAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementKernelCartierDual

/-! # Complement Torsion Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementTorsionPairing.Construction

noncomputable section

/-! The canonical n-torsion pairing identifies the actual kernel of a
power complement with the Cartier dual of the original isogeny kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsCommMonObj A] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f] (r : B ⟶ A) [IsMonHom r]
  (n : ℕ) (hfr : f ≫ r = (𝟙 A) ^ n)
  (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (e : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A n) (B := Torsion.Groups.Construction.nativeTorsionScheme A n)
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

set_option backward.isDefEq.respectTransparency false in
def complementTorsionPairing :
    Annihilator.Construction.SchemeBicharacter (A := Picard.PoincareBundle.Kernel.Scheme.kernelObject (f ≫ r)) (B := Picard.PoincareBundle.Kernel.Scheme.kernelObject (f ≫ r))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  e.restrict (Kernel.HomEquality.Construction.kernelHomEqualityIso (f ≫ r) ((𝟙 A) ^ n) hfr).hom
    (Kernel.HomEquality.Construction.kernelHomEqualityIso (f ≫ r) ((𝟙 A) ^ n) hfr).hom

omit [IsCommMonObj B] in
set_option backward.isDefEq.respectTransparency false in
theorem complementTorsionPairing_isPerfect (he : e.toSheafPairing.IsPerfect) :
    (complementTorsionPairing f r n hfr e).toSheafPairing.IsPerfect :=
  e.restrict_isPerfect_of_scheme_iso he
    (Kernel.HomEquality.Construction.kernelHomEqualityIso (f ≫ r) ((𝟙 A) ^ n) hfr).hom

variable (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    e.relativeAnnihilator F = F)

include hf hlag in
set_option backward.isDefEq.respectTransparency false in
theorem complementTorsionPairing_selfAnnihilating :
    (complementTorsionPairing f r n hfr e).relativeAnnihilator
      (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup (Kernel.PreimageExactness.Construction.kernelPreimageInclusion f r)) =
        Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup (Kernel.PreimageExactness.Construction.kernelPreimageInclusion f r) := by
  have hlag' : e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf)) =
      Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf) := by
    simpa only [Poincare.BundleSelfAnnihilator.Construction.nativeTorsion_kernel_eq_e45_image f n hf] using hlag
  exact e.nativeImage_selfAnnihilation_transport
    (Kernel.HomEquality.Construction.kernelHomEqualityIso (f ≫ r) ((𝟙 A) ^ n) hfr).hom
    (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf) (Kernel.PreimageExactness.Construction.kernelPreimageInclusion f r)
    (Kernel.HomEquality.Construction.kernelPreimageInclusion_torsion_transport f r n hfr hf) hlag'

variable [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  [IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom] [Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom]
  [LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom]

set_option backward.isDefEq.respectTransparency false in
def complementKernelCartierIsoOfTorsion (he : e.toSheafPairing.IsPerfect)
    (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f))) :
    Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject r) ≅ Y.dual := by
  have hl := complementTorsionPairing_selfAnnihilating f r n hfr hf e hlag
  have : Mono (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r).hom.hom :=
    inferInstanceAs (Mono (Kernel.PreimageExactness.Construction.kernelPreimageInclusion f r))
  exact ComplementKernelCartierDual.Construction.complementKernelCartierGroupIso f r (complementTorsionPairing f r n hfr e).toSheafPairing
    (complementTorsionPairing_isPerfect f r n hfr e he)
    ((complementTorsionPairing f r n hfr e).nativeImage_selfAnnihilation_sheaf
      (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r) hl) Y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementTorsionPairing.Construction
