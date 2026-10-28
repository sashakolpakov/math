import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementaryKernelIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.IsoExponent

/-! # Coprime Complement Kernel Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeComplementKernelComparison.Construction

noncomputable section

/-! The actual coprime polarization-kernel isomorphism identifies the
source-map kernel with the kernel of the original quotient complement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

universe u
variable {S : Scheme.{u}} {A B C Z : Over S}
  [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj Z] [IsCommMonObj A] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (q : B ⟶ C) [IsMonHom q] [IsFinite q.left] [Flat q.left] [Surjective q.left]
  (g : C ⟶ Z) [IsMonHom g] (φ : A ⟶ Z) [IsMonHom φ]
  (n d : ℕ) (hnd : n.Coprime d) (hcomp : f ≫ q ≫ g = φ ^ n)
  (hφ : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (e : Picard.PoincareBundle.Kernel.Scheme.kernelObject φ ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject q) [IsMonHom e.hom]
  (he : e.hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion φ ≫ f)

include hnd hcomp hφ hf e he in
theorem exists_coprime_complement_kernel_comparison :
    ∃ r : B ⟶ A, IsMonHom r ∧ f ≫ r = (𝟙 A) ^ n ∧ r ≫ f = (𝟙 B) ^ n ∧
      ∃ eK : Picard.PoincareBundle.Kernel.Scheme.kernelObject r ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject g,
        eK.hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ q := by
  obtain ⟨r, hrmon, hfr, hrf⟩ := FppfPowerComplement.Construction.exists_fppf_power_complement f n hf
  have : IsMonHom r := hrmon
  have : EffectiveEpi f := Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_over_of_fpqc f
  have h : r ≫ φ = q ≫ g := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, hfr, MonObj.pow_comp, Category.id_comp, hcomp]
  have hφf (T : Over S) (x : T ⟶ A) (hx : x ≫ φ = 1) : (x ≫ f) ≫ q = 1 := by
    let z := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv φ T).symm ⟨x, hx⟩
    have hz : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion φ = x :=
      congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv φ T).apply_symm_apply ⟨x, hx⟩)
    have hxf : x ≫ f = (z ≫ e.hom) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q := by
      rw [← hz, Category.assoc, ← he, ← Category.assoc]
    rw [hxf, Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]
  let eK := ComplementaryKernelIso.Construction.complementaryKernelIso f r q g φ h n d hnd hfr hrf hφ hφf
    (Kernel.IsoExponent.Construction.kernelIso_transports_exponent φ q e d hφ)
  exact ⟨r, hrmon, hfr, hrf, eK,
    ComplementaryKernelIso.Construction.complementaryKernelIso_inclusion f r q g φ h n d hnd hfr hrf hφ hφf
      (Kernel.IsoExponent.Construction.kernelIso_transports_exponent φ q e d hφ)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeComplementKernelComparison.Construction
