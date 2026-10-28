import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Total

/-! # Ambient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientCoordinates

noncomputable section

/-! A local diagram whose terminal object is an ambient open has the
same supported Čech complex as the relative open-cover construction.
Only its nonempty tuple products need to be preserved. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {X : TopCat.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C)
  [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]

def objectHom (n : ℕ) (a : AugmentedOrdered.Cech.Index ι n) :
    F.obj ((AugmentedOrdered.Cech.formal U n).obj a) ⟶
      F.obj (⊤_ C) ⊓ (AugmentedOrdered.Cech.formal (F.obj ∘ U) n).obj a :=
  homOfLE (le_inf (leOfHom (F.map (terminal.from _)))
    (leOfHom (piComparison F (U ∘ a.val))))

def objectInv (n : ℕ) (a : AugmentedOrdered.Cech.Index ι n) :
    F.obj (⊤_ C) ⊓ (AugmentedOrdered.Cech.formal (F.obj ∘ U) n).obj a ⟶
      F.obj ((AugmentedOrdered.Cech.formal U n).obj a) := by
  cases n with
  | zero => exact homOfLE inf_le_left ≫ F.map (AugmentedOrdered.CechZero.emptyProductMap U a)
  | succ n => exact homOfLE inf_le_right ≫ (PreservesProduct.iso F (U ∘ a.val)).inv

def objectIso (n : ℕ) (a : AugmentedOrdered.Cech.Index ι n) :
    F.obj ((AugmentedOrdered.Cech.formal U n).obj a) ≅
      F.obj (⊤_ C) ⊓ (AugmentedOrdered.Cech.formal (F.obj ∘ U) n).obj a where
  hom := objectHom F U n a
  inv := objectInv F U n a

variable {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (P : (Opens X)ᵒᵖ ⥤ D)

def componentIso (n : ℕ) : AugmentedOrdered.Cech.object U (F.op ⋙ P) n ≅
    AugmentedOrdered.Cech.object (F.obj ∘ U) ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op ⋙ P) n :=
  Pi.mapIso (fun a : AugmentedOrdered.Cech.Index ι n => P.mapIso (objectIso F U n a).symm.op)

omit [Preadditive D] in
theorem component_hom_π (n : ℕ) (a : AugmentedOrdered.Cech.Index ι n) :
    (componentIso F U P n).hom ≫
        Pi.π (fun b : AugmentedOrdered.Cech.Index ι n => P.obj
          (op (F.obj (⊤_ C) ⊓ (AugmentedOrdered.Cech.formal (F.obj ∘ U) n).obj b))) a =
      Pi.π (fun b : AugmentedOrdered.Cech.Index ι n => P.obj (op (F.obj ((AugmentedOrdered.Cech.formal U n).obj b)))) a ≫
        P.map (objectIso F U n a).inv.op := Pi.mapIso_hom_π _ _

omit [Preadditive D] in
theorem coface_naturality (n : ℕ) (k : Fin (n + 1)) :
    AugmentedOrdered.Cech.coface U (F.op ⋙ P) n k ≫ (componentIso F U P (n + 1)).hom =
      (componentIso F U P n).hom ≫
        AugmentedOrdered.Cech.coface (F.obj ∘ U) ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op ⋙ P) n k := by
  apply AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.productIso_natural
    (fun a : AugmentedOrdered.Cech.Index ι n => P.mapIso (objectIso F U n a).symm.op)
    (fun a : AugmentedOrdered.Cech.Index ι (n + 1) => P.mapIso (objectIso F U (n + 1) a).symm.op)
    (fun a => a.delete k)
    (fun a => P.map (F.map ((AugmentedOrdered.Cech.face U n k).φ a)).op)
    (fun a => P.map ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).map
      ((AugmentedOrdered.Cech.face (F.obj ∘ U) n k).φ a)).op)
  intro a
  exact (P.map_comp _ _).symm.trans
    ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))

theorem differential_naturality (n : ℕ) :
    AugmentedOrdered.Cech.differential U (F.op ⋙ P) n ≫ (componentIso F U P (n + 1)).hom =
      (componentIso F U P n).hom ≫
        AugmentedOrdered.Cech.differential (F.obj ∘ U) ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op ⋙ P) n := by
  simp only [AugmentedOrdered.Cech.differential, comp_sum, sum_comp, comp_zsmul, zsmul_comp, coface_naturality]

def iso : AugmentedOrdered.Cech.complex U (F.op ⋙ P) ≅
    AugmentedOrdered.Cech.complex (F.obj ∘ U) ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op ⋙ P) :=
  HomologicalComplex.Hom.isoOfComponents (componentIso F U P) (by
    intro n m h
    obtain rfl : m = n + 1 := h.symm
    dsimp only [AugmentedOrdered.Cech.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact (differential_naturality F U P n).symm)

theorem naturality {Q : (Opens X)ᵒᵖ ⥤ D} (a : P ⟶ Q) :
    AugmentedOrdered.CechFunctor.complexMap U (Functor.whiskerLeft F.op a) ≫ (AmbientCoordinates.iso F U Q).hom =
      (AmbientCoordinates.iso F U P).hom ≫ AugmentedOrdered.CechFunctor.complexMap (F.obj ∘ U)
        (Functor.whiskerLeft (RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op a) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.productIso_natural
    (fun b : AugmentedOrdered.Cech.Index ι n => P.mapIso (objectIso F U n b).symm.op)
    (fun b : AugmentedOrdered.Cech.Index ι n => Q.mapIso (objectIso F U n b).symm.op)
    id (fun b => a.app (op (F.obj ((AugmentedOrdered.Cech.formal U n).obj b))))
    (fun b => a.app (op (F.obj (⊤_ C) ⊓ (AugmentedOrdered.Cech.formal (F.obj ∘ U) n).obj b)))
  intro b
  exact (a.naturality (objectIso F U n b).inv.op).symm

def functorIso :
    (Functor.whiskeringLeft Cᵒᵖ (Opens X)ᵒᵖ D).obj F.op ⋙
      AugmentedOrdered.CechFunctor.functor U ≅
        RelativeCech.Total.localFunctor (F.obj (⊤_ C)) (F.obj ∘ U) :=
  NatIso.ofComponents (AmbientCoordinates.iso F U) (fun {_ _} a => AmbientCoordinates.naturality F U _ a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientCoordinates
