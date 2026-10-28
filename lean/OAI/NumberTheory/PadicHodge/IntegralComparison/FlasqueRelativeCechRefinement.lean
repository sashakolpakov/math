import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SupportedCechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.EdgeRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement

/-! # Flasque Relative Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueRelativeCechRefinement

noncomputable section

/-! The actual relative and global ordered refinements of a flasque
module-sheaf complex are invertible, with independent coefficient universe. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem iso_of_triangle {D : Type*} [Category D] {A B C : D}
    (a : A ⟶ B) (b : A ⟶ C) (f : B ⟶ C) [IsIso a] [IsIso b]
    (h : a ≫ f = b) : IsIso f := by
  have hf : f = inv a ≫ b := by
    apply (cancel_epi a).mp
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using h
  rw [hf]
  infer_instance

universe u w z
variable (R : Type u) [CommRing R] (X : Scheme.{0})
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u w} R)) ℕ)
  (hK : ∀ q, TopCat.Presheaf.IsFlasque (X := X.toTopCat) (K.X q).obj)

local instance coefficient_limits : HasLimitsOfSize.{0,0} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{0,0,z,u}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) :=
  ModuleCat.hasColimitsOfSize.{z,u,0,0} R

abbrev presheaf := FlasqueOrderedGlobal.underlying.{u,w} R X.toTopCat K

variable (A : X.Opens) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

include hK in
theorem rows (q n : ℕ) :
    ((Supported.OrderedCechEdge.bicomplex.{u,0,0,w} R X.toTopCat
      (RelativeCech.Intersections.intersect A) U K).X q).ExactAt (n+1) := by
  let := hK q
  let : ∀ (d : ℕ) (a : Fin (d+1) → ι),
      PreservesLimit (Discrete.functor (U ∘ a)) (RelativeCech.Intersections.intersect A) :=
    fun _ a => RelativeCech.RefinementQuasiIso.intersection_preserves_product A (U ∘ a)
  exact FlasqueOrderedRows.exactAt_succ.{u,w} R X.toTopCat
    (RelativeCech.Intersections.intersect A) U (K.X q) n

include hK in
theorem relative (O : X.Opens) (hU : ∀ i, A ⊓ U i ≤ O) (hV : ∀ i, A ⊓ V i ≤ O)
    (hcU : A ⊓ O ≤ ⨆ i, A ⊓ U i) (hcV : A ⊓ O ≤ ⨆ i, A ⊓ V i) (q : ℕ) :
    IsIso (RelativeCech.Refinement.homology A U V r (presheaf.{u,w} R X K) q) := by
  change IsIso (homologyMap (AugmentedOrdered.CechRefinementTotal.totalMap U V r
    (Supported.OrderedCechEdge.presheafComplex.{u,0,0,w} R X.toTopCat
      (RelativeCech.Intersections.intersect A) K)) q)
  exact Module.SupportedCechRefinement.isIso.{u,0,0,w} R X.toTopCat
    (RelativeCech.Intersections.intersect A) U V r O K hU hV
    (by exact (inf_le_inf_right O inf_le_left).trans hcU)
    (by exact (inf_le_inf_right O inf_le_left).trans hcV)
    (rows.{u,w} R X K hK A U) (rows.{u,w} R X K hK A V) q

include hK in
theorem ordered (hU : iSup U = ⊤) (hV : iSup V = ⊤) (q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap U V r (presheaf.{u,w} R X K)) q) := by
  let := FlasqueOrderedGlobal.homology_isIso.{u,w} R X.toTopCat U K hU hK q
  let := FlasqueOrderedGlobal.homology_isIso.{u,w} R X.toTopCat V K hV hK q
  exact iso_of_triangle _ _ _ (OrderedCech.EdgeRefinement.homology U V r (presheaf.{u,w} R X K) q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueRelativeCechRefinement
