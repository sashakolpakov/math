import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor
import Mathlib.Data.Fintype.Sort

/-! # Cech Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates

noncomputable section

/-! Exact intersection-coordinate formulas and the final intersection
of the augmented ordered Čech complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (P : Cᵒᵖ ⥤ D)

omit [Preadditive D] in
theorem coface_comp_pi (n : ℕ) (k : Fin (n + 1)) (a : Cech.Index ι (n + 1)) :
    Cech.coface U P n k ≫ Pi.π (fun b : Cech.Index ι (n + 1) => P.obj (op ((Cech.formal U (n + 1)).obj b))) a =
      Pi.π (fun b : Cech.Index ι n => P.obj (op ((Cech.formal U n).obj b))) (a.delete k) ≫
        P.map ((Cech.face U n k).φ a).op := by
  exact Pi.lift_comp_π _ a

theorem differential_comp_pi (n : ℕ) (a : Cech.Index ι (n + 1)) :
    Cech.differential U P n ≫ Pi.π (fun b : Cech.Index ι (n + 1) => P.obj (op ((Cech.formal U (n + 1)).obj b))) a =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        (Pi.π (fun b : Cech.Index ι n => P.obj (op ((Cech.formal U n).obj b))) (a.delete k) ≫
          P.map ((Cech.face U n k).φ a).op) := by
  simp only [Cech.differential, sum_comp, zsmul_comp, coface_comp_pi]

omit [Preadditive D] in
theorem objectMap_comp_pi {Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (n : ℕ) (a : Cech.Index ι n) :
    CechFunctor.objectMap U f n ≫ Pi.π (fun b : Cech.Index ι n => Q.obj (op ((Cech.formal U n).obj b))) a =
      Pi.π (fun b : Cech.Index ι n => P.obj (op ((Cech.formal U n).obj b))) a ≫
        f.app (op ((Cech.formal U n).obj a)) := by
  exact Pi.map_π (fun b : Cech.Index ι n => f.app (op ((Cech.formal U n).obj b))) a

variable [Fintype ι] (g : ℕ) (hg : Fintype.card ι = g)

def topIndex : Cech.Index ι g := ⟨monoEquivOfFin ι hg, (monoEquivOfFin ι hg).strictMono⟩

theorem topIndex_unique (a : Cech.Index ι g) : a = topIndex g hg := by
  have hs : Function.Surjective a.val :=
    ((Fintype.bijective_iff_injective_and_card a.val).mpr
      ⟨a.property.injective, by simpa using hg.symm⟩).2
  apply Subtype.ext
  apply (a.property.range_inj_of_wellFoundedLT (topIndex g hg).property).mp
  change Set.range a.val = Set.range (monoEquivOfFin ι hg)
  rw [Set.range_eq_univ.mpr hs, Set.range_eq_univ.mpr (monoEquivOfFin ι hg).surjective]

def topObject : C := (Cech.formal U g).obj (topIndex g hg)

def topFactorIso (a : Cech.Index ι g) : topObject U g hg ≅ (Cech.formal U g).obj a :=
  eqToIso (congrArg (Cech.formal U g).obj (topIndex_unique g hg a).symm)

def topInclusion : P.obj (op (topObject U g hg)) ⟶ Cech.object U P g :=
  Pi.lift (fun a : Cech.Index ι g => P.map (topFactorIso U g hg a).inv.op)

omit [Preadditive D] in
theorem topInclusion_comp_pi (a : Cech.Index ι g) :
    topInclusion U P g hg ≫ Pi.π (fun b : Cech.Index ι g => P.obj (op ((Cech.formal U g).obj b))) a =
      P.map (topFactorIso U g hg a).inv.op := Pi.lift_comp_π _ a

omit [Preadditive D] in
theorem topInclusion_naturality {Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) :
    topInclusion U P g hg ≫ CechFunctor.objectMap U f g =
      f.app (op (topObject U g hg)) ≫ topInclusion U Q g hg := by
  change (Pi.lift (fun b : Cech.Index ι g => P.map (topFactorIso U g hg b).inv.op)) ≫
    (Limits.Pi.map (fun b : Cech.Index ι g => f.app (op ((Cech.formal U g).obj b)))) =
      f.app (op (topObject U g hg)) ≫
        Pi.lift (fun b : Cech.Index ι g => Q.map (topFactorIso U g hg b).inv.op)
  apply Pi.hom_ext
  intro a
  rw [Category.assoc, Pi.map_π, ← Category.assoc, Pi.lift_comp_π,
    Category.assoc, Pi.lift_comp_π]
  exact f.naturality _

include hg in
theorem differential_top : Cech.differential U P g = 0 := by
  apply Pi.hom_ext
  intro a
  have hcard := Fintype.card_le_of_injective a.val a.property.injective
  simp only [Fintype.card_fin, hg] at hcard
  omega

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates
