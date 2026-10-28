import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.SubgroupComparisons

/-! # Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.Kernel

noncomputable section

/-! The whole original chosen/opposite kernel passes to its parameter
scheme with its actual pairing and every factor retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelProducts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.SubgroupComparisons
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative

universe u

variable {S : Scheme.{u}} {s : ℕ} (A : Grp (Over S)) [IsCommMonObj A.X]
  (G H : Fin s → Grp (Over S)) [∀ v, IsCommMonObj (G v).X] [∀ v, IsCommMonObj (H v).X]
  (i : ∀ v, G v ⟶ A) (j : ∀ v, H v ⟶ A) (P : Over S)
  (e : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := (G v).X) (B := (H v).X)
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
  (active : Fin s) (c : Fin s → Bool) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.X P)

omit [∀ v, IsCommMonObj (G v).X] in
theorem relativeParameter_chosen (v : Fin s) :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P
      (Kernel.Base.chosenKernel (fun w => (G w).X) (fun w => (i w).hom.hom) active c F v) =
    Kernel.Base.chosenKernel (fun w => ((Over.pullback P.hom).mapGrp.obj (G w)).X)
      (fun w => ((Over.pullback P.hom).mapGrp.map (i w)).hom.hom) active c
      (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P F) v := by
  classical
  unfold Kernel.Base.chosenKernel
  split_ifs
  · rfl
  · exact SubgroupComparisons.relativeParameter_fixed_kernel (G v) A P (i v)
  · exact KernelProducts.relativeParameter_trivial A P

omit [IsCommMonObj A.X] in
theorem relativeParameter_opposite (v : Fin s) :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P
      (Kernel.Base.forcedOpposite (fun w => (G w).X) (fun w => (H w).X)
        (fun w => (i w).hom.hom) (fun w => (j w).hom.hom) e v F) =
    Kernel.Base.forcedOpposite (fun w => ((Over.pullback P.hom).mapGrp.obj (G w)).X)
      (fun w => ((Over.pullback P.hom).mapGrp.obj (H w)).X)
      (fun w => ((Over.pullback P.hom).mapGrp.map (i w)).hom.hom)
      (fun w => ((Over.pullback P.hom).mapGrp.map (j w)).hom.hom)
      (fun w => AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback P.hom (G w) (H w) (e w)) v
      (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P F) := by
  unfold Kernel.Base.forcedOpposite
  rw [← ImageComparison.relativeParameter_image_comparison, AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison.Construction.relativeParameter_annihilator_comparison,
    SubgroupComparisons.relativeParameter_pullback_comparison]

theorem relativeParameter_fullKernel :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P
      (Kernel.Base.fullKernel (fun w => (G w).X) (fun w => (H w).X)
        (fun w => (i w).hom.hom) (fun w => (j w).hom.hom) e active c F) =
    Kernel.Base.fullKernel (fun w => ((Over.pullback P.hom).mapGrp.obj (G w)).X)
      (fun w => ((Over.pullback P.hom).mapGrp.obj (H w)).X)
      (fun w => ((Over.pullback P.hom).mapGrp.map (i w)).hom.hom)
      (fun w => ((Over.pullback P.hom).mapGrp.map (j w)).hom.hom)
      (fun w => AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback P.hom (G w) (H w) (e w)) active c
      (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P F) := by
  unfold Kernel.Base.fullKernel
  rw [KernelProducts.relativeParameter_tuple]
  congr 1
  funext v
  rw [KernelProducts.relativeParameter_product, relativeParameter_opposite, relativeParameter_chosen]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.Kernel
