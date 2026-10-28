import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.HomFiberFaithfulness

/-! # Composite Field Hom Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Homomorphisms in a family pulled back through a field are detected by one field-valued point of a connected test scheme, including nonreduced tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S T : Scheme.{u}} {K F : Type u} [Field K] [Field F] {g h : ℕ}

theorem Abelian.Schemes.AbelianScheme.compositePullback_hom_eq_of_field_fiber
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (b : Spec (.of K) ⟶ S) (t : T ⟶ Spec (.of K)) [PreconnectedSpace T]
    (s : Spec (.of F) ⟶ T)
    (f q : (A.pullback (t ≫ b)).scheme ⟶ (B.pullback (t ≫ b)).scheme)
    [IsMonHom f] [IsMonHom q]
    (hfq : (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let a := A.pullbackCompIso b t
  let c := B.pullbackCompIso b t
  let f' := a.inv ≫ f ≫ c.hom
  let q' := a.inv ≫ q ≫ c.hom
  have hf' : IsMonHom f' := inferInstance
  have hq' : IsMonHom q' := inferInstance
  have hp : (Over.pullback s).map f' = (Over.pullback s).map q' := by
    simp only [f', q', Functor.map_comp, hfq]
  have he : f' = q' :=
    (A.pullback b).pullback_hom_eq_of_field_fiber (B.pullback b) t s f' q' hp
  exact (cancel_epi a.inv).mp ((cancel_mono c.hom).mp (by simpa only [f', q', Category.assoc] using he))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
