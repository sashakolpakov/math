import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.RelativeAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingIsoAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.SubobjectDetection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectBlocks

/-! # Image Pairing Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Scheme-valued self-annihilation transports along the actual
ambient group isomorphism and gives equality of the native sheaf subobjects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B H : Over S} [GrpObj A] [GrpObj B] [GrpObj H]

theorem Intrinsic.ImagePairingTransport.Construction.nativeImage_pullback_of_mono
    (f : B ⟶ A) [IsMonHom f] [Mono f] (i : H ⟶ A) [IsMonHom i]
    (j : H ⟶ B) [IsMonHom j] (h : j ≫ f = i) :
    SubgroupTransport.Construction.relativeSubgroupPullback f (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i) = Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup j := by
  ext T t x
  change (∃ y, y ≫ i = x ≫ f) ↔ ∃ y, y ≫ j = x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (cancel_mono f).mp (by rw [Category.assoc, h]; exact hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Category.assoc, h]⟩

theorem Annihilator.Construction.SchemeBicharacter.restrict_isPerfect_of_scheme_iso [IsCommMonObj A] [IsCommMonObj B]
    (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := A) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (he : e.toSheafPairing.IsPerfect) (f : B ⟶ A) [IsMonHom f] [IsIso f] :
    (e.restrict f f).toSheafPairing.IsPerfect := by
  have : IsMonHom (inv f ≫ f) := by rw [IsIso.inv_hom_id]; infer_instance
  have : IsMonHom (inv f) := Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp (inv f) f
  apply e.restrict_isPerfect he f (inv f) (IsIso.hom_inv_id f)
    f (inv f) (IsIso.hom_inv_id f)
  intro T x y
  rw [IsIso.inv_hom_id, Category.comp_id, Category.comp_id]

theorem Annihilator.Construction.SchemeBicharacter.nativeImage_selfAnnihilation_transport
    (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := A) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (f : B ⟶ A) [IsMonHom f] [IsIso f] (i : H ⟶ A) [IsMonHom i]
    (j : H ⟶ B) [IsMonHom j] (h : j ≫ f = i)
    (hlag : e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i) = Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i) :
    (e.restrict f f).relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup j) = Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup j := by
  rw [← Intrinsic.ImagePairingTransport.Construction.nativeImage_pullback_of_mono f i j h, e.restrict_annihilator_iso, hlag]

variable [IsCommMonObj A] [IsCommMonObj H]

theorem Annihilator.Construction.SchemeBicharacter.nativeImage_selfAnnihilation_sheaf
    (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := A) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (i : Grp.mk H ⟶ Grp.mk A) [Mono i.hom.hom]
    (hlag : e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom) =
      Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom) :
    CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i) = Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i := by
  apply Sheaf.SubobjectDetection.Construction.sheafSubobject_eq_of_sections
  intro T
  ext y
  obtain ⟨y⟩ := y
  change T ⟶ A at y
  let t : T ⟶ Over.mk (𝟙 S) := Over.homMk T.hom (Category.comp_id _)
  have hm := e.nativeImage_annihilator_membership i.hom.hom T t y
  rw [hlag] at hm
  exact (e.toSheafPairing_annihilator_sections i T y).trans
    (hm.symm.trans (Sheaf.AnnihilatorSections.Construction.mem_nativeSubgroupSheaf_sections i T y).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
