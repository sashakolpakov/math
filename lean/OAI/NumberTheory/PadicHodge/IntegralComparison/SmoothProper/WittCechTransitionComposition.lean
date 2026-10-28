import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleTransitionComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransition

/-! # Witt Cech Transition Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionComposition

noncomputable section

/-! The original Čech transition maps satisfy all inverse-system identities. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

universe u v w z

private theorem map_op_identity {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{z} D] (H : Cᵒᵖ ⥤ D) {A : C} {f : A ⟶ A} (e : f = 𝟙 A) :
    H.map f.op = 𝟙 _ := by
  subst f
  exact H.map_id _

private theorem map_op_composition {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{z} D] (H : Cᵒᵖ ⥤ D) {A B E : C}
    {f : A ⟶ B} {g : B ⟶ E} {h : A ⟶ E} (e : f ≫ g = h) :
    H.map g.op ≫ H.map f.op = H.map h.op :=
  (H.map_comp g.op f.op).symm.trans (congrArg (fun a => H.map a.op) e)

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem coefficient_identity (n a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    WittCechTransitionData.coefficient p k X n n le_rfl a t = 𝟙 _ := by
  let H := BigCrystallineCohomology.largePresheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X)
  exact map_op_identity H (WittTupleTransitionComposition.identity p k X n a t)

theorem coefficient_composition (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    WittCechTransitionData.coefficient p k X m l hml a t ≫ WittCechTransitionData.coefficient p k X n m hnm a t =
      WittCechTransitionData.coefficient p k X n l (hnm.trans hml) a t :=
  map_op_composition (BigCrystallineCohomology.largePresheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
    (WittTupleTransitionComposition.composition p k X n m l hnm hml a t)

theorem identity (n : ℕ) : WittCechTransition.map p k X n n le_rfl = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext a
  exact (congrArg (fun c => Limits.Pi.map c) (funext (coefficient_identity p k X n a))).trans Limits.Pi.map_id

theorem composition (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    WittCechTransition.map p k X m l hml ≫ WittCechTransition.map p k X n m hnm =
      WittCechTransition.map p k X n l (hnm.trans hml) := by
  apply HomologicalComplex.Hom.ext
  funext a
  exact (Limits.Pi.map_comp_map (WittCechTransitionData.coefficient p k X m l hml a) (WittCechTransitionData.coefficient p k X n m hnm a)).trans
    (congrArg (fun c => Limits.Pi.map c) (funext (coefficient_composition p k X n m l hnm hml a)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionComposition
