import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleHomGluing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Module Local Factorization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleLocalFactorization

noncomputable section

/-! Local factorizations through a monomorphism glue as actual module
maps, using the native sheaf of linear morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleHomGluing

variable {X : Scheme.{u}} (M : X.Modules) {N P : X.Modules} (a : N ⟶ P)

def postcompose : (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).obj ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M P).obj where
  app U := TypeCat.ofHom fun q ↦
    ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomFromOver M P U.unop (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomToOver M N U.unop q ≫ a.over U.unop)
  naturality {U V} f := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext m
    rfl

theorem postcompose_global (b : M ⟶ N) (U : X.Opens) :
    (postcompose M a).app (op U) (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomFromOver M N U (b.over U)) =
      ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomFromOver M P U ((b ≫ a).over U) := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  ext m
  rfl

theorem mono_over [Mono a] (U : X.Opens) : Mono (a.over U) := by
  have : Mono a.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map a))
  have hm : Mono (a.over U).val := PresheafOfModules.mono_of_injective
    (fun {V} ↦ PresheafOfModules.injective_of_mono a.val (op V.unop.left))
  exact (SheafOfModules.forget (X.ringCatSheaf.over U)).mono_of_mono_map hm

theorem postcompose_injective [Mono a] (U : X.Opens) :
    Function.Injective ((postcompose M a).app (op U)) := by
  intro b c hbc
  apply (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomOverEquiv M N U).injective
  have : Mono (a.over U) := mono_over a U
  apply (cancel_mono (a.over U)).mp
  exact congrArg (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomToOver M P U) hbc

theorem existsUnique_local_factorization [Mono a] (b : M ⟶ P)
    {ι : Type*} (U : ι → X.Opens) (hU : (⊤ : X.Opens) ≤ iSup U)
    (q : ∀ i, (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).obj.obj (op (U i)))
    (hq : ∀ i, (postcompose M a).app (op (U i)) (q i) =
      ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomFromOver M P (U i) (b.over (U i))) :
    ∃! c : M ⟶ N, c ≫ a = b := by
  let F := (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).obj
  let G := (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M P).obj
  let β := postcompose M a
  let s := (ModuleHomGluing.moduleHomGlobalEquiv M P).symm b
  have hq' (i) : β.app (op (U i)) (q i) = G.map (homOfLE le_top).op s :=
    (hq i).trans (ModuleHomGluing.moduleHomGlobalEquiv_symm_restrict M P b (U i)).symm
  have hc : TopCat.Presheaf.IsCompatible F U q := by
    intro i j
    apply postcompose_injective M a (U i ⊓ U j)
    have hi := β.naturality_apply (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (q i)
    have hj := β.naturality_apply (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (q j)
    have hi' := congrArg (fun r ↦ r s)
      (G.map_comp (homOfLE (show U i ≤ ⊤ from le_top)).op
        (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op)
    have hj' := congrArg (fun r ↦ r s)
      (G.map_comp (homOfLE (show U j ≤ ⊤ from le_top)).op
        (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op)
    exact hi.trans ((congrArg (fun r ↦ G.map
      (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op r) (hq' i)).trans
        (hi'.symm.trans (hj'.trans ((congrArg (fun r ↦ G.map
          (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op r) (hq' j)).symm.trans hj.symm))))
  obtain ⟨c, hc, _⟩ := ModuleHomGluing.existsUnique_hom_of_local_maps M N U hU q hc
  have hfact : c ≫ a = b := by
    apply (ModuleHomGluing.moduleHomGlobalEquiv M P).symm.injective
    let H : TopCat.Sheaf (Type u) X := ⟨G, (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M P).property⟩
    apply H.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) hU
    intro i
    rw [ModuleHomGluing.moduleHomGlobalEquiv_symm_restrict, ModuleHomGluing.moduleHomGlobalEquiv_symm_restrict,
      ← postcompose_global, hc i, hq i]
  exact ⟨c, hfact, fun d hd ↦ (cancel_mono a).mp (hd.trans hfact.symm)⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleLocalFactorization
