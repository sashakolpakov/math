import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReductionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Differential

/-! # Witt Cech Transition Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

noncomputable section

/-! Canonical quotient maps on the actual global Witt frame Čech terms, retaining their native coefficient action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u v w z

private theorem contravariantSquare {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{z} D] (H : Cᵒᵖ ⥤ D)
    {A B C' D' : C} {f : A ⟶ B} {g : B ⟶ D'} {h : A ⟶ C'} {i : C' ⟶ D'}
    (e : f ≫ g = h ≫ i) : H.map i.op ≫ H.map h.op = H.map g.op ≫ H.map f.op := by
  exact (H.map_comp i.op h.op).symm.trans
    ((congrArg (fun q => H.map q.op) e.symm).trans (H.map_comp g.op f.op))

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

def sections (n : ℕ) : (WittTupleFlatness.Objects p k X n)ᵒᵖ ⥤ ModuleCat.{u + 1} R :=
  (BoundedCrystalline.Site.inclusion (Witt.Crystalline.wittStructureMap p k X) n).op ⋙
    BigCrystallineCohomology.largePresheaf (Witt.Crystalline.wittStructureMap p k X)

def complex (n : ℕ) : CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  BoundedFrame.CechComplex.presheafComplex (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n)

def coordinate (n a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) : (complex p k X n).X a ⟶
    (sections p k X n).obj (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t)) :=
  Pi.π (fun t => (sections p k X n).obj
    (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t))) t

def coefficient (n m : ℕ) (hnm : n ≤ m) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    (sections p k X m).obj (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t)) ⟶
      (sections p k X n).obj (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t)) :=
  (BigCrystallineCohomology.largePresheaf (Witt.Crystalline.wittStructureMap p k X)).map
    (WittTupleReduction.morphism p k X n m hnm a t).op

theorem coefficient_naturality (n m : ℕ) (hnm : n ≤ m) (a b : ℕ)
    (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → StandardCover.Index k X) :
    coefficient p k X n m hnm b (t ∘ θ) ≫ (sections p k X n).map
      (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X n) θ t).op =
        (sections p k X m).map (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X m) θ t).op ≫
          coefficient p k X n m hnm a t := by
  let H := BigCrystallineCohomology.largePresheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X)
  exact contravariantSquare H
    (WittTupleReductionNaturality.natural p k X n m hnm a b θ t)

def termMap (n m : ℕ) (hnm : n ≤ m) (a : ℕ) : (complex p k X m).X a ⟶ (complex p k X n).X a :=
  Limits.Pi.map (fun t => coefficient p k X n m hnm a t)

theorem termMap_coordinate (n m : ℕ) (hnm : n ≤ m) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    termMap p k X n m hnm a ≫ coordinate p k X n a t =
      coordinate p k X m a t ≫ coefficient p k X n m hnm a t :=
  Pi.map_π _ t

theorem differential_coordinate (n a : ℕ) (t : Fin (a + 2) → StandardCover.Index k X) (x : (complex p k X n).X a) :
    coordinate p k X n (a + 1) t ((complex p k X n).d a (a + 1) x) =
      ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) •
        (sections p k X n).map (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X n) i.succAbove t).op
          (coordinate p k X n a (t ∘ i.succAbove) x) :=
  FrameCech.Differential.coordinates.{u + 1, u} (WittFrameFamily.Family.frame p k X n) R (sections p k X n) a t x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData
