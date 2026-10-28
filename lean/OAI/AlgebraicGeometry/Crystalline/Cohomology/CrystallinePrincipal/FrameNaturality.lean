import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FrameMaps

/-! # Frame Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FrameNaturality.CrystallinePrincipalFrameNaturality

noncomputable section

/-!
# Naturality of native frame forms on principal opens

The localization equivalences with the actual associated module sheaf
commute with every principal-open inclusion. Equality follows from the
localized-module universal property and the native projection identities.
-/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)

local notation "QR" => Q.thickening.ring

def coefficients : (PrincipalCoefficient.PrincipalCoefficientCategory.Object QR)ᵒᵖ ⥤ ModuleCat.{u} QR :=
  (PrincipalCoefficient.PrincipalCoefficientCategory.opensFunctor QR).op ⋙
    (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.associatedSheaf p k B σ Q n).obj

variable {r s : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring} (f : r ⟶ s)

include f in
theorem target_units (t : Submonoid.powers s.val) :
    IsUnit (algebraMap QR
      (Module.End QR ((coefficients p k B σ Q n).obj (op r))) t) := by
  let M := CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n
  have hu := (tilde (R := CommRingCat.of QR) M).isUnit_algebraMap_end_of_le_basicOpen s.val
    (show Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR r.val ≤
      Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR s.val from leOfHom f)
  obtain ⟨m, hm⟩ := t.property
  change s.val ^ m = (t : QR) at hm
  rw [← hm, map_pow]
  exact hu.pow m

theorem sections_naturality :
    (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.sectionsEquiv p k B σ a Q n r.val).toLinearMap.comp
      (FrameMaps.CrystallinePrincipalFrameMaps.moduleMap p k B σ a Q f n) =
    ((coefficients p k B σ Q n).map f.op).hom.comp
      (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.sectionsEquiv p k B σ a Q n s.val).toLinearMap := by
  apply IsLocalizedModule.ext (Submonoid.powers s.val)
    (CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization.termMap p k B σ a Q s.val n)
    (target_units p k B σ Q n f)
  apply LinearMap.ext
  intro x
  have hl := (congrArg (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.sectionsEquiv p k B σ a Q n r.val)
    (LinearMap.congr_fun (FrameMaps.CrystallinePrincipalFrameMaps.moduleMap_comp p k B σ a Q f n) x)).trans
      (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.sectionsEquiv_termMap p k B σ a Q n r.val x)
  have hr₁ := congrArg (((coefficients p k B σ Q n).map f.op).hom)
    (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.sectionsEquiv_termMap p k B σ a Q n s.val x)
  have hr₂ := congrArg (fun h : (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) ⟶
      (coefficients p k B σ Q n).obj (op r) => h.hom x)
    (tilde.toOpen_res (R := CommRingCat.of QR) (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n)
      (Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR s.val) (Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR r.val)
      ((PrincipalCoefficient.PrincipalCoefficientCategory.opensFunctor QR).map f))
  exact hl.trans (hr₁.trans hr₂).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FrameNaturality.CrystallinePrincipalFrameNaturality
