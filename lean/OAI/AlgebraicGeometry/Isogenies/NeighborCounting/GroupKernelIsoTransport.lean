import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.IsoTransport

/-! # Group Kernel Iso Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupKernelIsoTransport

noncomputable section

/-! Full-kernel transport stated on the original bundled group objects,
with all underlying group-preservation proofs supplied by their morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.IsoTransport

universe u

variable {S : Scheme.{u}} (A B : Grp (Over S)) [IsCommMonObj A.X] [IsCommMonObj B.X]
  (e : A ≅ B) {s : ℕ} (G H U V : Fin s → Grp (Over S))
  (d : ∀ v, G v ≅ H v) (r : ∀ v, U v ≅ V v)
  (i : ∀ v, G v ⟶ A) (j : ∀ v, H v ⟶ B) (k : ∀ v, U v ⟶ A) (l : ∀ v, V v ⟶ B)
  {W P : Over S} [GrpObj W]
  (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := (H v).X) (B := (V v).X) (W := W))
  (active : Fin s) (c : Fin s → Bool) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup B.X P)

theorem group_fullKernel_iso_transport
    (hd : ∀ v, (d v).hom.hom.hom ≫ (j v).hom.hom = (i v).hom.hom ≫ e.hom.hom.hom)
    (hr : ∀ v, (r v).hom.hom.hom ≫ (l v).hom.hom = (k v).hom.hom ≫ e.hom.hom.hom) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom.hom.hom
      (Kernel.Base.fullKernel (fun v => (H v).X) (fun v => (V v).X)
        (fun v => (j v).hom.hom) (fun v => (l v).hom.hom) pairing active c F) =
    Kernel.Base.fullKernel (fun v => (G v).X) (fun v => (U v).X)
      (fun v => (i v).hom.hom) (fun v => (k v).hom.hom)
      (fun v => (pairing v).restrict (d v).hom.hom.hom (r v).hom.hom.hom)
      active c (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom.hom.hom F) := by
  let eraw : A.X ≅ B.X := (Grp.forget (Over S)).mapIso e
  let draw (v) : (G v).X ≅ (H v).X := (Grp.forget (Over S)).mapIso (d v)
  let rraw (v) : (U v).X ≅ (V v).X := (Grp.forget (Over S)).mapIso (r v)
  have : IsMonHom eraw.hom := e.hom.hom.isMonHom_hom
  have : ∀ v, IsMonHom (draw v).hom := fun v => (d v).hom.hom.isMonHom_hom
  have : ∀ v, IsMonHom (rraw v).hom := fun v => (r v).hom.hom.isMonHom_hom
  have : ∀ v, IsMonHom (i v).hom.hom := fun v => (i v).hom.isMonHom_hom
  have : ∀ v, IsMonHom (j v).hom.hom := fun v => (j v).hom.isMonHom_hom
  have : ∀ v, IsMonHom (k v).hom.hom := fun v => (k v).hom.isMonHom_hom
  have : ∀ v, IsMonHom (l v).hom.hom := fun v => (l v).hom.isMonHom_hom
  exact Kernel.IsoTransport.fullKernel_iso_transport eraw (fun v => (G v).X) (fun v => (H v).X)
    (fun v => (U v).X) (fun v => (V v).X) draw rraw
    (fun v => (i v).hom.hom) (fun v => (j v).hom.hom)
    (fun v => (k v).hom.hom) (fun v => (l v).hom.hom) hd hr pairing active c F

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupKernelIsoTransport
