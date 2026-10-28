import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.Kernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupKernelIsoTransport

/-! # Kernel Iso Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelIsoComparison

noncomputable section

/-! Compare the full original parameter families through the actual
ambient and block isomorphisms, retaining every chosen and opposite factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.Kernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupKernelIsoTransport
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative

universe u

variable {S T Q : Scheme.{u}} (f : Q ⟶ S) (g : Q ⟶ T)
  (A : Grp (Over S)) (B : Grp (Over T)) [IsCommMonObj A.X] [IsCommMonObj B.X]
  (e : (Over.pullback f).mapGrp.obj A ≅ (Over.pullback g).mapGrp.obj B)
  {s : ℕ} (G U : Fin s → Grp (Over S)) (H V : Fin s → Grp (Over T))
  [∀ v, IsCommMonObj (G v).X] [∀ v, IsCommMonObj (U v).X]
  [∀ v, IsCommMonObj (H v).X] [∀ v, IsCommMonObj (V v).X]
  (d : ∀ v, (Over.pullback f).mapGrp.obj (G v) ≅ (Over.pullback g).mapGrp.obj (H v))
  (r : ∀ v, (Over.pullback f).mapGrp.obj (U v) ≅ (Over.pullback g).mapGrp.obj (V v))
  (i : ∀ v, G v ⟶ A) (j : ∀ v, H v ⟶ B) (k : ∀ v, U v ⟶ A) (l : ∀ v, V v ⟶ B)
  (pairA : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := (G v).X) (B := (U v).X)
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
  (pairB : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := (H v).X) (B := (V v).X)
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T).X))
  (active : Fin s) (c : Fin s → Bool)
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.X (Over.mk f)) (J : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup B.X (Over.mk g))

theorem parameter_fullKernel_iso_comparison
    (hd : ∀ v, (d v).hom.hom.hom ≫ ((Over.pullback g).mapGrp.map (j v)).hom.hom =
      ((Over.pullback f).mapGrp.map (i v)).hom.hom ≫ e.hom.hom.hom)
    (hr : ∀ v, (r v).hom.hom.hom ≫ ((Over.pullback g).mapGrp.map (l v)).hom.hom =
      ((Over.pullback f).mapGrp.map (k v)).hom.hom ≫ e.hom.hom.hom)
    (hp : ∀ v, (AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback g (H v) (V v) (pairB v)).restrict
      (d v).hom.hom.hom (r v).hom.hom.hom = AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f (G v) (U v) (pairA v))
    (hactive : AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom.hom.hom (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter B (Over.mk g) J) =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A (Over.mk f) F) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom.hom.hom
      (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter B (Over.mk g)
        (Kernel.Base.fullKernel (fun v => (H v).X) (fun v => (V v).X)
          (fun v => (j v).hom.hom) (fun v => (l v).hom.hom) pairB active c J)) =
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A (Over.mk f)
      (Kernel.Base.fullKernel (fun v => (G v).X) (fun v => (U v).X)
        (fun v => (i v).hom.hom) (fun v => (k v).hom.hom) pairA active c F) := by
  rw [Kernel.relativeParameter_fullKernel, Kernel.relativeParameter_fullKernel]
  have h := GroupKernelIsoTransport.group_fullKernel_iso_transport
    ((Over.pullback f).mapGrp.obj A) ((Over.pullback g).mapGrp.obj B) e
    (fun v => (Over.pullback f).mapGrp.obj (G v)) (fun v => (Over.pullback g).mapGrp.obj (H v))
    (fun v => (Over.pullback f).mapGrp.obj (U v)) (fun v => (Over.pullback g).mapGrp.obj (V v)) d r
    (fun v => (Over.pullback f).mapGrp.map (i v)) (fun v => (Over.pullback g).mapGrp.map (j v))
    (fun v => (Over.pullback f).mapGrp.map (k v)) (fun v => (Over.pullback g).mapGrp.map (l v))
    (fun v => AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback g (H v) (V v) (pairB v)) active c
    (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter B (Over.mk g) J) hd hr
  have hp' : (fun v => (AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback g (H v) (V v) (pairB v)).restrict
      (d v).hom.hom.hom (r v).hom.hom.hom) =
      (fun v => AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f (G v) (U v) (pairA v)) := funext hp
  rw [hp', hactive] at h
  exact h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelIsoComparison
