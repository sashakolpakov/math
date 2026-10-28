import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelCartierComparison

/-! # Etale Kernel Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleKernelModels

noncomputable section

/-! The all-test kernel functor has its actual finite locally free
model. For a morphism between finite etale groups, the required
geometry follows from the original structural maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

def finiteFlatMorphismKernelModel
    {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f]
    [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left] :
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f).Model := by
  let : GrpObj (Picard.PoincareBundle.Kernel.Scheme.kernelObject f) := Picard.PoincareBundle.Kernel.Scheme.kernelGroup f
  obtain ⟨hfinite, hflat, hfp⟩ := AbelianScheme.IsogenyQuotient.Intrinsic.KernelCartierComparison.Construction.categoricalKernel_finiteLocallyFree f
  let : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom := hfinite
  let : Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom := hflat
  let : LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom := hfp
  rw [AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel_scheme_image]
  exact AbelianScheme.IsogenyQuotient.Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup_model (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f)

def finiteEtaleMorphismKernelModel
    {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsFinite A.hom] [Etale A.hom] [IsFinite B.hom] [Etale B.hom]
    (f : A ⟶ B) [IsMonHom f] : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f).Model := by
  have : IsFinite (f.left ≫ B.hom) := f.w.symm ▸ inferInstanceAs (IsFinite A.hom)
  have : IsFinite f.left := IsFinite.of_comp f.left B.hom
  have : Etale (f.left ≫ B.hom) := f.w.symm ▸ inferInstanceAs (Etale A.hom)
  have : Etale f.left := Etale.of_comp f.left B.hom
  exact finiteFlatMorphismKernelModel f

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleKernelModels
