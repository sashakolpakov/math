import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DegreeParameterTorsion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.GeometricKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnramifiedTorsionDetection

/-! # Zero Picard Kernel Exactness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ZeroPicardKernelExactness.Construction

noncomputable section

/-! Degree loci and norm torsion prove the actual Cartier kernel
comparison over any scheme over a characteristic-zero field. No
constant degree or extra degree-unit premise is supplied. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] (f : X ⟶ A.scheme) [IsMonHom f]

theorem canonicalPicardPullback_kernel_precomp {T U : Over S}
    (z : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
    (hz : Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T z = 1) (a : U ⟶ T) :
    Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f U (a ≫ z) = 1 := by
  have hm : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.map a.op (1 : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.obj (op T)) = 1 := by
    have h := (Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf X) a.op).map_one
    simp only [Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply] at h
    exact h
  exact (Canonical.PicardPullback.Construction.canonicalPicardPullbackHom_natural D f a z).symm.trans
    ((congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.map a.op) hz).trans hm)

variable [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  {Q : Over S} [GrpObj Q] [IsCommMonObj Q] [IsProper Q.hom]
  (q : (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme ⟶ Q) [IsMonHom q]
  (hkill : Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C ≫ q = 1)

include hkill in
set_option backward.isDefEq.respectTransparency false in
theorem charZeroPicardPullback_kernel_quotient_zero
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k)) (T : Over S)
    (z : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
    (hz : Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T z = 1) : z ≫ q = 1 := by
  let d (t : T.left) := Relative.DegreeLoci.Construction.relativeFiniteFlatDegree f (T.hom t)
  let V (t : T.left) : T.left.Opens := T.hom ⁻¹ᵁ Relative.DegreeLoci.Construction.relativeDegreeOpen f (d t)
  have hcover : iSup V = ⊤ := by
    ext t
    exact iff_true_intro (TopologicalSpace.Opens.mem_iSup.mpr ⟨t, rfl⟩)
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (T.left.openCoverOfIsOpenCover V hcover)
  intro t
  let U : Over S := Over.mk ((V t).ι ≫ T.hom)
  let a : U ⟶ T := Over.homMk (V t).ι rfl
  let w := a ≫ z
  have hw : Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f U w = 1 := canonicalPicardPullback_kernel_precomp D f z hz a
  have hpow : w ^ d t = 1 := DegreeParameterTorsion.Construction.canonicalPicardKernel_pow_of_base_degree D f (d t) U
    (fun u => u.property) w hw
  have hd : 0 < d t := Relative.DegreeBaseChange.Construction.relativeDegree_pos f (T.hom t)
  have he : w ≫ q = 1 := by
    apply UnramifiedTorsionDetection.Construction.invertibleTorsion_section_eq_one_of_geometric_points Q (d t)
      (Relative.DegreeBaseChange.Construction.positiveNat_isUnit_on_charZero_field_scheme p (d t) hd) (w ≫ q)
      (by rw [← MonObj.pow_comp, hpow, MonObj.one_comp])
    intro K _ _ s x
    obtain ⟨c, hc⟩ := RelativePicard.GeometricKernel.Construction.canonicalPicardPullback_geometric_kernel_lift D f C s (x ≫ w)
      (canonicalPicardPullback_kernel_precomp D f w hw x)
    rw [← Category.assoc, ← hc, Category.assoc, hkill, MonObj.comp_one]
  have he' := congrArg Over.Hom.left he
  change (V t).ι ≫ z.left ≫ q.left = (V t).ι ≫ (1 : T ⟶ Q).left
  exact he'.trans (congrArg Over.Hom.left (MonObj.comp_one a : a ≫ (1 : T ⟶ Q) = 1)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ZeroPicardKernelExactness.Construction
