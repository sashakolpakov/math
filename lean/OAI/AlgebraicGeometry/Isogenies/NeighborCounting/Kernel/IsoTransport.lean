import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubgroupIsoTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingIsoAnnihilator

/-! # Iso Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.IsoTransport

noncomputable section

/-! The whole chosen/opposite kernel transports through actual source
and block isomorphisms. The opposite comparison follows from the pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubgroupIsoTransport

universe u

theorem fixedKernelFamily_iso_square {S : Scheme.{u}} {A B G H P : Over S}
    [GrpObj A] [GrpObj B] [GrpObj G] [GrpObj H]
    (e : A ≅ B) [IsMonHom e.hom] (d : G ≅ H) [IsMonHom d.hom]
    (i : G ⟶ A) (j : H ⟶ B) [IsMonHom i] [IsMonHom j]
    (square : d.hom ≫ j = i ≫ e.hom) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (Base.fixedKernelFamily (P := P) j) = Base.fixedKernelFamily i := by
  have h := SubgroupIsoTransport.subgroupPullback_image_square e d i j square (Base.fixedKernelFamily (P := P) (𝟙 H))
  have hi : AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback d.hom (Base.fixedKernelFamily (P := P) (𝟙 H)) =
      Base.fixedKernelFamily (𝟙 G) := by
    ext T t x
    constructor
    · intro _
      exact ⟨x, Category.comp_id x⟩
    · intro _
      change ∃ y : T ⟶ H, y ≫ 𝟙 H = x ≫ d.hom
      exact ⟨x ≫ d.hom, Category.comp_id _⟩
  rw [hi] at h
  simpa only [Parameter.ImageComparison.fixedKernelFamily_image, Category.id_comp] using h

variable {S : Scheme.{u}} {A B P : Over S} [GrpObj A] [GrpObj B]
  [IsCommMonObj A] [IsCommMonObj B]
  (e : A ≅ B) [IsMonHom e.hom] {s : ℕ}
  (G H U V : Fin s → Over S)
  [∀ v, GrpObj (G v)] [∀ v, GrpObj (H v)] [∀ v, GrpObj (U v)] [∀ v, GrpObj (V v)]
  (d : ∀ v, G v ≅ H v) (r : ∀ v, U v ≅ V v)
  [∀ v, IsMonHom (d v).hom] [∀ v, IsMonHom (r v).hom]
  (i : ∀ v, G v ⟶ A) (j : ∀ v, H v ⟶ B)
  (k : ∀ v, U v ⟶ A) (l : ∀ v, V v ⟶ B)
  [∀ v, IsMonHom (i v)] [∀ v, IsMonHom (j v)]
  [∀ v, IsMonHom (k v)] [∀ v, IsMonHom (l v)]
  (chosenSquare : ∀ v, (d v).hom ≫ j v = i v ≫ e.hom)
  (oppositeSquare : ∀ v, (r v).hom ≫ l v = k v ≫ e.hom)
  {W : Over S} [GrpObj W]
  (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := H v) (B := V v) (W := W))
  (active : Fin s) (c : Fin s → Bool) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P)

include chosenSquare in
theorem chosenKernel_iso_transport (v : Fin s) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (Base.chosenKernel H j active c F v) =
      Base.chosenKernel G i active c (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom F) v := by
  classical
  unfold Base.chosenKernel
  split_ifs
  · rfl
  · exact fixedKernelFamily_iso_square e (d v) (i v) (j v) (chosenSquare v)
  · exact SubgroupIsoTransport.subgroupPullback_iso_trivial e

include chosenSquare oppositeSquare in
omit [IsCommMonObj A] [IsCommMonObj B] in
theorem forcedOpposite_iso_transport (v : Fin s) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (Base.forcedOpposite H V j l pairing v F) =
      Base.forcedOpposite G U i k (fun w => (pairing w).restrict (d w).hom (r w).hom) v
        (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom F) := by
  have hc : AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (i v) (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom F) =
      AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (d v).hom (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (j v) F) := by
    ext T t x
    change (x ≫ i v) ≫ e.hom ∈ F.points T t ↔ (x ≫ (d v).hom) ≫ j v ∈ F.points T t
    rw [Category.assoc, Category.assoc, chosenSquare v]
  have ha := (pairing v).restrict_annihilator_iso (d v).hom (r v).hom
    (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (j v) F)
  have hb := (congrArg ((pairing v).restrict (d v).hom (r v).hom).relativeAnnihilator hc).trans ha
  exact (SubgroupIsoTransport.subgroupPullback_image_square e (r v) (k v) (l v) (oppositeSquare v)
    ((pairing v).relativeAnnihilator (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (j v) F))).trans
      (congrArg (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage (k v)) hb.symm)

include chosenSquare oppositeSquare in
theorem fullKernel_iso_transport :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (Base.fullKernel H V j l pairing active c F) =
      Base.fullKernel G U i k (fun w => (pairing w).restrict (d w).hom (r w).hom) active c
        (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom F) := by
  unfold Base.fullKernel
  rw [SubgroupIsoTransport.subgroupPullback_iso_tuple]
  congr 1
  funext v
  rw [SubgroupIsoTransport.subgroupPullback_iso_product,
    forcedOpposite_iso_transport e G H U V d r i j k l chosenSquare oppositeSquare,
    chosenKernel_iso_transport e G H d i j chosenSquare]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.IsoTransport
