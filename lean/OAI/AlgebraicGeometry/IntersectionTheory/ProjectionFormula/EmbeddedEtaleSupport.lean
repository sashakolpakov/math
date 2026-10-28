import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Stalk

/-! # Embedded Etale Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedEtaleSupport

noncomputable section

/-! Etaleness on a closed embedded integral scheme transfers to the
native reduced support of its image, including the chosen stalk point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {Z X Y : Scheme} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Y)

theorem exists_open (U : Z.Opens) [Etale (U.ι ≫ (i ≫ f))] (z : Z) (hz : z ∈ U)
    (hx : i z ∈ (Closed.ImmersionSupport.support i : Set X)) :
    ∃ V : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (Closed.ImmersionSupport.support i)).Opens,
      CycleClass.Thom.IntersectionGeometry.supportPreimage (Closed.ImmersionSupport.support i) (i z) hx ∈ V ∧
      Etale (V.ι ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι (Closed.ImmersionSupport.support i) ≫ f)) := by
  let B := Closed.ImmersionSupport.support i
  let e := Closed.ImmersionSupport.supportIso i
  let V := e.inv ⁻¹ᵁ U
  let j : (V : Scheme) ⟶ U := e.inv.resLE U V le_rfl
  have he : e.inv ≫ i = CycleClass.Geometric.GenericPoint.reducedSupportι B := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (Closed.ImmersionSupport.supportIso_fac i).symm
  have hproj : j ≫ (U.ι ≫ (i ≫ f)) = V.ι ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ f) := by
    dsimp only [j]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, ← Category.assoc e.inv,
      he]
  have hp : e.inv (CycleClass.Thom.IntersectionGeometry.supportPreimage B (i z) hx) = z := by
    apply i.isClosedEmbedding.injective
    have ht := congrArg (fun g : CycleClass.Geometric.GenericPoint.reducedSupportScheme B ⟶ X => g (CycleClass.Thom.IntersectionGeometry.supportPreimage B (i z) hx)) he
    exact ht.trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec B (i z) hx)
  refine ⟨V, ?_, ?_⟩
  · change e.inv (CycleClass.Thom.IntersectionGeometry.supportPreimage B (i z) hx) ∈ U
    exact hp.symm ▸ hz
  · rw [← hproj]
    infer_instance

theorem stalk_properties (U : Z.Opens) [Etale (U.ι ≫ (i ≫ f))] (z : Z) (hz : z ∈ U)
    (hx : i z ∈ (Closed.ImmersionSupport.support i : Set X)) :
    (Support.Stalk.Projection.map f (Closed.ImmersionSupport.support i) (i z) hx).hom.Flat ∧
    (Support.Stalk.Projection.map f (Closed.ImmersionSupport.support i) (i z) hx).hom.FormallyUnramified ∧
    (Support.Stalk.Projection.map f (Closed.ImmersionSupport.support i) (i z) hx).hom.EssFiniteType := by
  obtain ⟨V, hv, hV⟩ := exists_open i f U z hz hx
  let := hV
  exact Support.Stalk.Projection.of_etale_open f (Closed.ImmersionSupport.support i) (i z) hx V hv

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedEtaleSupport
