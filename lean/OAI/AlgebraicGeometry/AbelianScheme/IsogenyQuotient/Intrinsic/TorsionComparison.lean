import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafComparison

/-! # Torsion Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionComparison.Construction

noncomputable section

/-!
The IsogenyQuotient native kernel and TorsionQuotient's torsion equalizer have their original
inclusions and homomorphism restrictions under the canonical scheme
isomorphism. This comparison preserves actual isomorphisms of torsion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)

theorem torsionEqualizerKernelIso_hom_inclusion :
    (Torsion.Groups.Construction.torsionEqualizerKernelIso A n).hom ≫ Torsion.Groups.Construction.nativeTorsionInclusion A n = TorsionQuotient.SubgroupFunctor.torsionι A n :=
  Torsion.Groups.Construction.nativeTorsionLift_inclusion A n (TorsionQuotient.SubgroupFunctor.torsionι A n)
    ((TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (TorsionQuotient.SubgroupFunctor.torsionι A n)).mp ⟨𝟙 _, Category.id_comp _⟩)

theorem torsionEqualizerKernelIso_inv_inclusion :
    (Torsion.Groups.Construction.torsionEqualizerKernelIso A n).inv ≫ TorsionQuotient.SubgroupFunctor.torsionι A n = Torsion.Groups.Construction.nativeTorsionInclusion A n :=
  TorsionQuotient.SubgroupFunctor.torsionLift_ι n (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Torsion.Groups.Construction.nativeTorsionInclusion_killed A n)

variable {A} {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem nativeTorsionMap_equalizer_comparison (f : A ⟶ B) [IsMonHom f] :
    Torsion.Groups.Construction.nativeTorsionMap n f = (Torsion.Groups.Construction.torsionEqualizerKernelIso A n).inv ≫
      CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso B n).hom := by
  apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion B n)).mp
  rw [Torsion.Groups.Construction.nativeTorsionMap_inclusion, Category.assoc, Category.assoc,
    torsionEqualizerKernelIso_hom_inclusion,
    CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion, ← Category.assoc,
    torsionEqualizerKernelIso_inv_inclusion]

theorem nativeTorsionMap_isIso_of_equalizer (f : A ⟶ B) [IsMonHom f]
    [IsIso (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n)] : IsIso (Torsion.Groups.Construction.nativeTorsionMap n f) := by
  rw [nativeTorsionMap_equalizer_comparison]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionComparison.Construction
