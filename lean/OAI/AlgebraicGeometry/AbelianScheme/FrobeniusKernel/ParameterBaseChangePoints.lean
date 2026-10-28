import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints

/-! # Parameter Base Change Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChangePoints.Construction

noncomputable section

/-! Two successive native kernel pullbacks retain exactly the same
original kernel point as the one-step pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters

variable {S S' : Scheme} (s : S' ⟶ S) (Q : Over S')
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

theorem parameterBaseChangeKernelPoint_left (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((Over.pullback s).map f))) :
    (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint ((Over.map s).obj Q).hom f U
        (z ≫ ParameterBaseChange.Construction.parameterBaseChangeKernelMap s Q f) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left =
    (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f ((Over.map Q.hom).obj U)
        (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom ((Over.pullback s).map f) U z) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left := by
  let f0 := (Over.pullback ((Over.map s).obj Q).hom).map f
  let f1 := (Over.pullback Q.hom).map ((Over.pullback s).map f)
  let k := ParameterBaseChange.Construction.parameterBaseChangeKernelMap s Q f
  let a := ParameterBaseChange.Construction.parameterBaseChangeInv s Q A
  let p := CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom ((Over.pullback s).map f) U z
  have h0 := congrArg Over.Hom.left
    (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion ((Over.map s).obj Q).hom f U (z ≫ k))
  have h1 := congrArg Over.Hom.left
    (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion Q.hom ((Over.pullback s).map f) U z)
  have h2 := congrArg Over.Hom.left
    (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion s f ((Over.map Q.hom).obj U) p)
  rw [CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.pullbackPoint_original_left] at h0 h1 h2
  have hm : ((z ≫ k) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f0).left = ((z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f1) ≫ a).left :=
    congrArg Over.Hom.left ((Category.assoc z k (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f0)).trans
      ((congrArg (fun t => z ≫ t) (ParameterBaseChange.Construction.parameterBaseChangeKernelMap_inclusion s Q f)).trans
        (Category.assoc z (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f1) a).symm))
  have hr := h2.trans (congrArg (fun t => t ≫ pullback.fst A.hom s) h1)
  exact h0.trans
    ((congrArg (fun t => t ≫ pullback.fst A.hom (Q.hom ≫ s)) hm).trans
      ((Category.assoc (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f1).left a.left (pullback.fst A.hom (Q.hom ≫ s))).trans
        ((congrArg (fun t => (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f1).left ≫ t)
          (ParameterBaseChange.Construction.parameterBaseChangeInv_projection s Q A)).trans
            ((Category.assoc (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f1).left
              (pullback.fst (pullback.snd A.hom s) Q.hom) (pullback.fst A.hom s)).symm.trans hr.symm))))

theorem parameterBaseChangeKernelPoint_original (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((Over.pullback s).map f))) :
    CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint ((Over.map s).obj Q).hom f U (z ≫ ParameterBaseChange.Construction.parameterBaseChangeKernelMap s Q f) =
      (ParameterBaseChange.Construction.parameterBaseChangeTestIso s Q U).inv ≫
        CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f ((Over.map Q.hom).obj U)
          (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom ((Over.pullback s).map f) U z) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f (1 : A ⟶ B)))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  apply Over.OverMorphism.ext
  change (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint ((Over.map s).obj Q).hom f U
      (z ≫ ParameterBaseChange.Construction.parameterBaseChangeKernelMap s Q f) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left =
    (𝟙 U.left ≫ (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f ((Over.map Q.hom).obj U)
      (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom ((Over.pullback s).map f) U z)).left) ≫ (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left
  rw [Category.id_comp]
  exact parameterBaseChangeKernelPoint_left s Q f U z

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChangePoints.Construction
