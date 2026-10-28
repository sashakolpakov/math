import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.AffinePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter

/-! # Closed Carrier Centers -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters.Construction

noncomputable section

/-! Extending actual centers from a closed carrier into its ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem kernel_comap_of_closed_pullback {S X T Y : Scheme.{u}}
    (g : S ⟶ Y) [IsClosedImmersion g] (g' : T ⟶ X) (i : T ⟶ S) (f : X ⟶ Y)
    (hpb : IsPullback g' i f g) : g.ker.comap f = g'.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← hpb.isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso]

theorem idealSheaf_closed_comap_map {X Y : Scheme.{u}}
    (q : Y ⟶ X) [IsClosedImmersion q] (K : Y.IdealSheafData) :
    (K.map q).comap q = K := by
  have hpb : IsPullback K.subschemeι (𝟙 K.subscheme) q (K.subschemeι ≫ q) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have h := kernel_comap_of_closed_pullback (K.subschemeι ≫ q) K.subschemeι (𝟙 _) q hpb
  simpa only [Scheme.IdealSheafData.map, Scheme.IdealSheafData.ker_subschemeι] using h

theorem closedCarrierCenter_contains_kernel {X Y : Scheme.{u}}
    (q : Y ⟶ X) (K : Y.IdealSheafData) : q.ker ≤ K.map q := by
  rw [← Scheme.IdealSheafData.map_bot]
  exact Scheme.IdealSheafData.map_mono q bot_le

theorem closedCarrierCenter_ne_bot {X Y : Scheme.{u}}
    (q : Y ⟶ X) [IsClosedImmersion q] (K : Y.IdealSheafData) (hK : K ≠ ⊥) :
    K.map q ≠ ⊥ := by
  intro h
  have he := congrArg (fun I : X.IdealSheafData => I.comap q) h
  rw [idealSheaf_closed_comap_map, Scheme.IdealSheafData.comap_bot] at he
  exact hK he

theorem closedCarrierCenter_smooth {X Y : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (q : Y ⟶ X) [IsClosedImmersion q]
    (K : Y.IdealSheafData) [Smooth (K.subschemeι ≫ (q ≫ f))] :
    Smooth ((K.map q).subschemeι ≫ f) := by
  let i := K.subschemeι ≫ q
  have hi : inv i.toImage ≫ i = i.imageι :=
    (IsIso.inv_comp_eq i.toImage).mpr i.toImage_imageι.symm
  change Smooth (i.imageι ≫ f)
  rw [← hi, Category.assoc]
  let : Smooth (i ≫ f) := by
    change Smooth ((K.subschemeι ≫ q) ≫ f)
    rw [Category.assoc]
    infer_instance
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters.Construction
