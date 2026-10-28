import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeComplementKernelComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementTorsionPairing

/-! # Coprime Kernel Cartier Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeKernelCartierIso.Construction

noncomputable section

/-! Coprime source-kernel comparison and full torsion self-annihilation
give an actual Cartier-dual isomorphism for the Picard source-map kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

universe u
variable {S : Scheme.{u}} {A B C Z : Over S}
  [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj Z]
  [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]
  (q : B ⟶ C) [IsMonHom q] [IsFinite q.left] [Flat q.left] [Surjective q.left]
  (g : C ⟶ Z) [IsMonHom g]
  [IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject g).hom] [Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject g).hom]
  [LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject g).hom]
  (φ : A ⟶ Z) [IsMonHom φ]
  (n d : ℕ) (hnd : n.Coprime d) (hcomp : f ≫ q ≫ g = φ ^ n)
  (hφ : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (eK : Picard.PoincareBundle.Kernel.Scheme.kernelObject φ ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject q) [IsMonHom eK.hom]
  (heK : eK.hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion φ ≫ f)
  (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A n) (B := Torsion.Groups.Construction.nativeTorsionScheme A n)
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
  (hb : b.toSheafPairing.IsPerfect)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    b.relativeAnnihilator F = F)
  (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f)))

include hnd hcomp hφ hf eK heK b hb hlag in
theorem coprimeKernel_cartierSheafIso :
    Nonempty (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject g)) ≅
      CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f)))) := by
  obtain ⟨r, hr, hfr, _hrf, j, hj⟩ :=
    CoprimeComplementKernelComparison.Construction.exists_coprime_complement_kernel_comparison f q g φ n d hnd hcomp hφ hf eK heK
  have : IsMonHom r := hr
  have : IsMonHom (j.hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g) := by rw [hj]; infer_instance
  have : IsMonHom j.hom := Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp j.hom (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g)
  have : IsIso j.hom.left := (Over.forget S).map_isIso j.hom
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom := by rw [← j.hom.w]; infer_instance
  have : Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom := by rw [← j.hom.w]; infer_instance
  have : LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom := by rw [← j.hom.w]; infer_instance
  have hl := ComplementTorsionPairing.Construction.complementTorsionPairing_selfAnnihilating f r n hfr hf b hlag
  have : Mono (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r).hom.hom :=
    inferInstanceAs (Mono (Kernel.PreimageExactness.Construction.kernelPreimageInclusion f r))
  exact ⟨(CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbIso (Grp.mkIso' j)).symm ≪≫
    ComplementKernelCartierDual.Construction.complementKernelCartierSheafIso f r (ComplementTorsionPairing.Construction.complementTorsionPairing f r n hfr b).toSheafPairing
      (ComplementTorsionPairing.Construction.complementTorsionPairing_isPerfect f r n hfr b hb)
      ((ComplementTorsionPairing.Construction.complementTorsionPairing f r n hfr b).nativeImage_selfAnnihilation_sheaf
        (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r) hl)⟩

include hnd hcomp hφ hf eK heK b hb hlag in
omit [IsCommMonObj C] in
theorem coprimeKernel_cartierIso : Nonempty (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject g) ≅ Y.dual) := by
  obtain ⟨r, hr, hfr, _hrf, j, hj⟩ :=
    CoprimeComplementKernelComparison.Construction.exists_coprime_complement_kernel_comparison f q g φ n d hnd hcomp hφ hf eK heK
  have : IsMonHom r := hr
  have : IsMonHom (j.hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g) := by rw [hj]; infer_instance
  have : IsMonHom j.hom := Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp j.hom (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g)
  have : IsIso j.hom.left := (Over.forget S).map_isIso j.hom
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom := by rw [← j.hom.w]; infer_instance
  have : Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom := by rw [← j.hom.w]; infer_instance
  have : LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom := by rw [← j.hom.w]; infer_instance
  exact ⟨(Grp.mkIso' j).symm ≪≫ ComplementTorsionPairing.Construction.complementKernelCartierIsoOfTorsion f r n hfr hf b hlag hb Y⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeKernelCartierIso.Construction
