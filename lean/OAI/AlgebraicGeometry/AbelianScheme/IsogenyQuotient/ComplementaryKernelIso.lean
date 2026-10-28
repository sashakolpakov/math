import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementaryKernelMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeKernelAdjustment
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfPowerComplement
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.DecompositionQuotient

/-! # Complementary Kernel Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementaryKernelIso.Construction

noncomputable section

/-! A coprime kernel adjustment identifies the complementary kernel
with the Picard source-map kernel through the actual quotient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

universe u
variable {S : Scheme.{u}} {A B C Z : Over S}
  [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj Z] [IsCommMonObj A] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f] (r : B ⟶ A) [IsMonHom r]
  (q : B ⟶ C) [IsMonHom q] (g : C ⟶ Z) [IsMonHom g] (φ : A ⟶ Z) [IsMonHom φ]
  (h : r ≫ φ = q ≫ g) (n d : ℕ) (hnd : n.Coprime d)
  (hfr : f ≫ r = (𝟙 A) ^ n) (hrf : r ≫ f = (𝟙 B) ^ n)
  (hφ : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → (x ≫ f) ≫ q = 1)
  (hq : ∀ (T : Over S) (x : T ⟶ B), x ≫ q = 1 → x ^ d = 1)

include h hnd hfr hφ hf in
theorem complementaryKernel_decomposition (T : Over S) (x : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject (q ≫ g)) :
    ∃ a : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject q, ∃ b : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject r,
      x ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (q ≫ g) = (a ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q) * (b ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r) := by
  let u := x ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (q ≫ g)
  have hu : (u ≫ r) ≫ φ = 1 := by
    rw [Category.assoc, h]
    change (x ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (q ≫ g)) ≫ (q ≫ g) = 1
    rw [Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]
  have hfr' (a : T ⟶ A) : (a ≫ f) ≫ r = a ^ n := by
    rw [Category.assoc, hfr, MonObj.comp_pow, Category.comp_id]
  obtain ⟨a, b, ha, hb, hab⟩ := CoprimeKernelAdjustment.Construction.coprimeKernel_adjustment (Picard.PoincareBundle.Kernel.Scheme.pointsMap φ T) (Picard.PoincareBundle.Kernel.Scheme.pointsMap f T)
    (Picard.PoincareBundle.Kernel.Scheme.pointsMap r T) (Picard.PoincareBundle.Kernel.Scheme.pointsMap q T) n d hnd hfr' (hφ T) (hf T) u hu
  refine ⟨(Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv q T).symm ⟨a, ha⟩, (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv r T).symm ⟨b, hb⟩, ?_⟩
  have ha' : (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv q T).symm ⟨a, ha⟩ ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q = a :=
    congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv q T).apply_symm_apply ⟨a, ha⟩)
  have hb' : (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv r T).symm ⟨b, hb⟩ ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r = b :=
    congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv r T).apply_symm_apply ⟨b, hb⟩)
  rw [ha', hb']
  exact hab

variable [IsFinite q.left] [Flat q.left] [Surjective q.left]

include h hnd hfr hrf hφ hf hq in
def complementaryKernelIso : Picard.PoincareBundle.Kernel.Scheme.kernelObject r ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject g := by
  have : Mono (ComplementaryKernelMap.Construction.complementaryKernelMap r q g φ h) :=
    ComplementaryKernelMap.Construction.complementaryKernelMap_mono r q g φ h n d hnd (FppfPowerComplement.Construction.powerComplement_kernel_torsion f r n hrf) hq
  exact Picard.PoincareBundle.Kernel.DecompositionQuotient.kernelIso q g r
    (ComplementaryKernelMap.Construction.complementaryKernelMap r q g φ h) (ComplementaryKernelMap.Construction.complementaryKernelMap_inclusion r q g φ h)
    (complementaryKernel_decomposition f r q g φ h n d hnd hfr hφ hf)

include hnd hfr hrf hφ hf hq in
theorem complementaryKernelIso_inclusion :
    (complementaryKernelIso f r q g φ h n d hnd hfr hrf hφ hf hq).hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g =
      Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ q :=
  ComplementaryKernelMap.Construction.complementaryKernelMap_inclusion r q g φ h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementaryKernelIso.Construction
