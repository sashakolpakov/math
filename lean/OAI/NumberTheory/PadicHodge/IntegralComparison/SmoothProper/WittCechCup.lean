import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialTransformation
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearNaturality

/-! # Witt Cech Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCup

noncomputable section

/-! Native Witt frames equip the original bounded crystalline Ext groups
with a cup product. The covering and acyclicity hypotheses are discharged
by the constructed smooth proper frame cover and bounded affine acyclicity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover

universe u v w z

private theorem contravariantSquare {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{z} D] (H : Cᵒᵖ ⥤ D)
    {A B C' D' : C} {a : A ⟶ B} {b : B ⟶ D'} {c : A ⟶ C'} {d : C' ⟶ D'}
    (e : a ≫ b = c ≫ d) : H.map d.op ≫ H.map c.op = H.map b.op ≫ H.map a.op :=
  (H.map_comp d.op c.op).symm.trans
    ((congrArg (fun q => H.map q.op) e.symm).trans (H.map_comp b.op a.op))

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "DP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "PIdeal" => Ideal.span {(p : WittVector p k)}

local instance separated : IsSeparated f := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev cochainAlgebra (n : ℕ) :=
  BoundedCrystalline.CechCup.cochainAlgebra f n (WittFrameFamily.Family.frame p k X n)

def equivalence (n i : ℕ) :
    (Cosimplicial.ModuleComplex.complex (cochainAlgebra p k X n)).homology i ≃ₗ[R]
      BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n i :=
  BoundedCrystalline.CechCup.cohomologyEquiv p k f n (WittFrameFamily.Family.frame p k X n)
    (WittFrameCover.covering p k X n) i

def cup (n i j : ℕ) :
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n i →ₗ[R]
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n j →ₗ[R]
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n (i + j) :=
  BoundedCrystalline.CechCup.cup p k f n (WittFrameFamily.Family.frame p k X n)
    (WittFrameCover.covering p k X n) i j

theorem cup_comparison (n i j : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (cochainAlgebra p k X n)).homology i)
    (y : (Cosimplicial.ModuleComplex.complex (cochainAlgebra p k X n)).homology j) :
    cup p k X n i j (equivalence p k X n i x) (equivalence p k X n j y) =
      equivalence p k X n (i + j)
        (Cosimplicial.ModuleCup.cohomologyCup (cochainAlgebra p k X n) i j x y) :=
  BoundedCrystalline.CechCup.cup_comparison p k f n (WittFrameFamily.Family.frame p k X n)
    (WittFrameCover.covering p k X n) i j x y

def algebraSections (n : ℕ) :
    (WittTupleFlatness.Objects p k X n)ᵒᵖ ⥤ CommAlgCat.{u + 1} R :=
  (BoundedCrystalline.Site.inclusion f n).op ⋙
    BoundedCrystalline.CechCup.structureAlgebraPresheaf f

def coefficient (n m : ℕ) (hnm : n ≤ m) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    (algebraSections p k X m).obj (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t)) ⟶
    (algebraSections p k X n).obj (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t)) :=
  (BoundedCrystalline.CechCup.structureAlgebraPresheaf f).map
    (WittTupleReduction.morphism p k X n m hnm a t).op

theorem coefficient_naturality (n m : ℕ) (hnm : n ≤ m) (a b : ℕ)
    (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → StandardCover.Index k X) :
    coefficient p k X n m hnm b (t ∘ θ) ≫ (algebraSections p k X n).map
      (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X n) θ t).op =
    (algebraSections p k X m).map
      (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X m) θ t).op ≫
        coefficient p k X n m hnm a t := by
  let H := BoundedCrystalline.CechCup.structureAlgebraPresheaf (p := p) (J := PIdeal) (δ := DP) f
  exact contravariantSquare H
    (WittTupleReductionNaturality.natural p k X n m hnm a b θ t)

local instance algebraProducts : HasProducts.{u} (CommAlgCat.{u + 1} R) := by
  have h : HasLimitsOfSize.{u, u} (CommAlgCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  exact fun I => h.has_limits_of_shape (Discrete I)

/-- The genuine ring quotient transitions preserve the full cosimplicial algebra. -/
def transition (n m : ℕ) (hnm : n ≤ m) : cochainAlgebra p k X m ⟶ cochainAlgebra p k X n :=
  Frame.CosimplicialTransformation.map.{u + 1, u} (WittFrameFamily.Family.frame p k X m) (WittFrameFamily.Family.frame p k X n)
    (algebraSections p k X m) (algebraSections p k X n)
    (coefficient p k X n m hnm) (coefficient_naturality p k X n m hnm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCup
