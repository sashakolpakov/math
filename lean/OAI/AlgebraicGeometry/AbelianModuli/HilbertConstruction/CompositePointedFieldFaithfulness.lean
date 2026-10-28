import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.PointedFieldFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMapBaseChange

/-! # Composite Pointed Field Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Identity-preserving maps in a family pulled back through a field are detected by one field-valued point on any connected test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem Abelian.Schemes.AbelianScheme.compositePullback_pointedMaps_eq_of_field_fiber
    {S T : Scheme.{u}} {K F : Type u} [Field K] [Field F] {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (b : Spec (.of K) ⟶ S) (t : T ⟶ Spec (.of K)) [PreconnectedSpace T]
    (s : Spec (.of F) ⟶ T)
    (f q : (A.pullback (t ≫ b)).scheme ⟶ (B.pullback (t ≫ b)).scheme)
    (hf : η[(A.pullback (t ≫ b)).scheme] ≫ f = η[(B.pullback (t ≫ b)).scheme])
    (hq : η[(A.pullback (t ≫ b)).scheme] ≫ q = η[(B.pullback (t ≫ b)).scheme])
    (hfq : (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let a := A.pullbackCompIso b t
  let c := B.pullbackCompIso b t
  have : IsMonHom a.hom := A.pullbackCompIso_preservesGroup b t
  have : IsMonHom c.hom := B.pullbackCompIso_preservesGroup b t
  have : IsMonHom a.symm.hom := inferInstanceAs (IsMonHom a.inv)
  have : IsMonHom c.symm.hom := inferInstanceAs (IsMonHom c.inv)
  let f' := a.inv ≫ f ≫ c.hom
  let q' := a.inv ≫ q ≫ c.hom
  have hf' : η[((A.pullback b).pullback t).scheme] ≫ f' = η[((B.pullback b).pullback t).scheme] :=
    (PointedMapBaseChange.pointedMap_conjugate_iff a.symm c.symm f).mpr hf
  have hq' : η[((A.pullback b).pullback t).scheme] ≫ q' = η[((B.pullback b).pullback t).scheme] :=
    (PointedMapBaseChange.pointedMap_conjugate_iff a.symm c.symm q).mpr hq
  have hp : (Over.pullback s).map f' = (Over.pullback s).map q' := by
    simp only [f', q', Functor.map_comp, hfq]
  have he : f' = q' :=
    (A.pullback b).pullback_pointedMaps_eq_of_field_fiber (B.pullback b) t s f' q' (hf'.trans hq'.symm) hp
  exact (cancel_epi a.inv).mp ((cancel_mono c.hom).mp (by simpa only [f', q', Category.assoc] using he))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
