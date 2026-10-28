import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechEdge
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Ordered Cech Exact -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechExact

noncomputable section

/-! The first supported Čech row is exact by separatedness of the
original sheaf on the complement. No acyclicity assumption is used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type w} [LinearOrder ι] (U : ι → C) (O : Opens X)

local instance coefficient_limits [UnivLE.{w, z}] :
    HasLimitsOfSize.{w, w} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, z, u}

local notation "V" => F.obj (⊤_ C)

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
  (ModuleCat.{max u v w z} R)) ℕ)
  (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))

include hO hcover in
theorem exact (q : ℕ) :
    (ShortComplex.mk (OrderedCechEdge.component.{u,v,w,z} R X F U O K q)
      (((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).X q).d 0 1)
      (OrderedCechEdge.cocycle.{u,v,w,z} R X F U O K hO q)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  let P : Cᵒᵖ ⥤ ModuleCat.{max u v w z} R := F.op ⋙ (K.X q).obj
  let e := AugmentedOrdered.CechZero.zeroIso (D := ModuleCat.{max u v w z} R) U P
  let r := (SectionsExcision.restriction V (V ⊓ O) inf_le_left).app (K.X q)
  let t := e.hom y
  have het : e.inv t = y := by
    exact ConcreteCategory.congr_hom e.hom_inv_id y
  have ht : r t = 0 := by
    apply TopCat.Sheaf.eq_of_locally_eq' (K.X q) (fun i => F.obj (U i)) (V ⊓ O)
      (fun i => homOfLE (le_inf (leOfHom (F.map (terminal.from (U i)))) (hO i))) hcover
    intro i
    rw [map_zero]
    let a : AugmentedOrdered.Cech.Index ι 1 :=
      ⟨fun _ => i, Subsingleton.strictMono (α := Fin 1) _⟩
    let T := (AugmentedOrdered.Cech.formal U 1).obj a
    have hz : P.map (terminal.from T).op t = 0 := by
      have hs := ConcreteCategory.congr_hom
        (AugmentedOrdered.CechZero.zeroIso_inv_differential_π U P a) t
      change (Pi.π (fun b : AugmentedOrdered.Cech.Index ι 1 =>
        P.obj (op ((AugmentedOrdered.Cech.formal U 1).obj b))) a)
          (AugmentedOrdered.Cech.differential U P 0 (e.inv t)) = _ at hs
      change AugmentedOrdered.Cech.differential U P 0 y = 0 at hy
      rw [het, hy, map_zero] at hs
      exact hs.symm
    let σ : U i ⟶ T := Pi.lift (fun _ : Fin 1 => 𝟙 (U i))
    have hs := congrArg ((K.X q).obj.map (F.map σ).op) hz
    rw [map_zero] at hs
    change (K.X q).obj.map (F.map σ).op
      ((K.X q).obj.map (F.map (terminal.from T)).op t) = 0 at hs
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← F.map_comp] at hs
    change (K.X q).obj.map _ ((K.X q).obj.map _ t) = 0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    have he : (homOfLE (le_inf (leOfHom (F.map (terminal.from (U i)))) (hO i)) ≫
        (homOfLE inf_le_left : V ⊓ O ⟶ V)) = F.map (σ ≫ terminal.from T) :=
      Subsingleton.elim _ _
    rw [he]
    exact hs
  refine ⟨(ModuleCat.kernelIsoKer r).inv ⟨t, ht⟩, ?_⟩
  change e.inv (kernel.ι r ((ModuleCat.kernelIsoKer r).inv ⟨t, ht⟩)) = y
  rw [ModuleCat.kernelIsoKer_inv_kernel_ι_apply]
  exact het

theorem mono (q : ℕ) :
    Mono (OrderedCechEdge.component.{u,v,w,z} R X F U O K q) := by
  change Mono ((SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q) ≫
    (AugmentedOrdered.CechZero.zeroIso (D := ModuleCat.{max u v w z} R) U
      (F.op ⋙ (K.X q).obj)).inv)
  change Mono (kernel.ι _ ≫ _)
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechExact
