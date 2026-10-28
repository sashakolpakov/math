import OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionBase
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplement
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Isogeny Kernel Torsion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyKernelTorsion

noncomputable section

/-! The actual scheme-theoretic kernel embeds into torsion using its
proved exponent. For a group obtained by scalar extension, the embedding
lands in the base change of the arithmetic torsion scheme, with its actual
ambient inclusion retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (n : ℕ)
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

def kernelIntoTorsion : Picard.PoincareBundle.Kernel.Scheme.kernelObject f ⟶ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n :=
  AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f) (hker _ _ (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp f))

@[reassoc] theorem kernelIntoTorsion_inclusion :
    kernelIntoTorsion f n hker ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f :=
  AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f) _

instance kernelIntoTorsion_isMonHom : IsMonHom (kernelIntoTorsion f n hker) := by
  have : Mono (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) := inferInstanceAs (Mono (equalizer.ι ((𝟙 A) ^ n) (1 : A ⟶ A)))
  have : IsMonHom (kernelIntoTorsion f n hker ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) := by
    rw [kernelIntoTorsion_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)

instance kernelIntoTorsion_mono : Mono (kernelIntoTorsion f n hker) := by
  constructor
  intro T x y hxy
  apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f)).mp
  exact (congrArg (fun a => x ≫ a) (kernelIntoTorsion_inclusion f n hker)).symm.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) hxy).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun a => y ≫ a) (kernelIntoTorsion_inclusion f n hker)))))

omit [GrpObj A] [IsCommMonObj A] [IsMonHom f] in
theorem kernel_etale [Etale f.left] : Etale (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom := by
  rw [Picard.PoincareBundle.Kernel.Scheme.kernel_hom_eq_snd f]
  exact MorphismProperty.of_isPullback (P := @Etale) (Picard.PoincareBundle.Kernel.Scheme.kernel_isPullback f) inferInstance

variable {S S' : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (φ : S' ⟶ S) {B : Over S'} [GrpObj B]
  (f : (Over.pullback φ).obj A ⟶ B) [IsMonHom f]
  (n : ℕ) (hker : ∀ (T : Over S') (x : T ⟶ (Over.pullback φ).obj A),
    x ≫ f = 1 → x ^ n = 1)

def kernelIntoArithmeticTorsion : Picard.PoincareBundle.Kernel.Scheme.kernelObject f ⟶ (Over.pullback φ).obj (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) :=
  kernelIntoTorsion f n hker ≫ (TorsionBase.TorsionBaseChange.schemeIso A n φ).hom

instance kernelIntoArithmeticTorsion_isMonHom : IsMonHom (kernelIntoArithmeticTorsion A φ f n hker) := by
  unfold kernelIntoArithmeticTorsion
  infer_instance

instance kernelIntoArithmeticTorsion_mono : Mono (kernelIntoArithmeticTorsion A φ f n hker) := by
  unfold kernelIntoArithmeticTorsion
  infer_instance

theorem kernelIntoArithmeticTorsion_inclusion :
    (kernelIntoArithmeticTorsion A φ f n hker).left ≫
      pullback.fst (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom φ ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left =
        (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f).left ≫ pullback.fst A.hom φ := by
  change ((kernelIntoTorsion f n hker).left ≫ (TorsionBase.TorsionBaseChange.schemeIso A n φ).hom.left) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (kernelIntoTorsion f n hker).left ≫ a)
      (TorsionBase.TorsionBaseChange.schemeIso_fst_inclusion A n φ)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun a => a ≫ pullback.fst A.hom φ)
            (congrArg Over.Hom.left (kernelIntoTorsion_inclusion f n hker)))))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyKernelTorsion
