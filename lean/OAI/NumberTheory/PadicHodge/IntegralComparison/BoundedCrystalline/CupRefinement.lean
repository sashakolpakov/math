import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.TupleRefinement

/-! # Cup Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CupRefinement

noncomputable section

/-! Actual geometric maps between bounded frame families give maps of the
native cosimplicial coefficient algebras. Their maps on the original
categorical module-complex homology preserve every cup product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

private theorem contravariantSquare {C : Type*} [Category* C]
    {D : Type*} [Category* D] (H : Cᵒᵖ ⥤ D)
    {A B C' D' : C} (a : A ⟶ B) (b : B ⟶ D') (c : A ⟶ C') (d : C' ⟶ D')
    (h : a ≫ b = c ≫ d) : H.map b.op ≫ H.map a.op = H.map d.op ≫ H.map c.op :=
  (H.map_comp b.op a.op).symm.trans
    ((congrArg (fun z => H.map z.op) h).trans (H.map_comp d.op c.op))

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY]
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {ι κ : Type u} (FX : ι → Site.Objects (p := p) (J := J) (δ := δ) f n)
  (FY : κ → Site.Objects (p := p) (J := J) (δ := δ) fY n) (ρ : ι → κ)
  (α : ∀ i, (BoundedOpen.Equivalence.postcompose g hg n).obj (FX i) ⟶ FY (ρ i))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "HX" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion
  (p := p) (J := J) (δ := δ) f n)) (CechCup.structureAlgebraPresheaf f)
local notation "HY" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion
  (p := p) (J := J) (δ := δ) fY n)) (CechCup.structureAlgebraPresheaf fY)

local instance algebraProducts : HasProducts.{u} (CommAlgCat.{u + 1} R) := by
  have h : HasLimitsOfSize.{u, u} (CommAlgCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  exact fun I => h.has_limits_of_shape (Discrete I)

def coefficient (a : ℕ) (t : Fin (a + 1) → ι) :
    (HY).obj (op (Presentation.TupleProducts.family.{u + 1, u} FY a (ρ ∘ t))) ⟶
      (HX).obj (op (Presentation.TupleProducts.family.{u + 1, u} FX a t)) :=
  (HY).map (Frame.TupleRefinement.map.{u + 1, u} G FX FY ρ α a t).op

theorem coefficient_naturality (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → ι) :
    coefficient g hg n FX FY ρ α b (t ∘ θ) ≫
        (HX).map (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} FX θ t).op =
      (HY).map (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} FY θ (ρ ∘ t)).op ≫
        coefficient g hg n FX FY ρ α a t :=
  contravariantSquare HY
    ((G).map (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} FX θ t))
    (Frame.TupleRefinement.map.{u + 1, u} G FX FY ρ α b (t ∘ θ))
    (Frame.TupleRefinement.map.{u + 1, u} G FX FY ρ α a t)
    (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} FY θ (ρ ∘ t))
    (Frame.TupleRefinement.naturality.{u + 1, u} G FX FY ρ α a b θ t)

def map : CechCup.cochainAlgebra fY n FY ⟶
    CechCup.cochainAlgebra f n FX :=
  Frame.CosimplicialRefinement.map.{u + 1, u} FY FX ρ HY HX
    (coefficient g hg n FX FY ρ α) (coefficient_naturality g hg n FX FY ρ α)

def complexMap := Cosimplicial.ModuleCup.complexMap (CupRefinement.map g hg n FX FY ρ α)

theorem cohomologyCup_natural (i j : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (CechCup.cochainAlgebra fY n FY)).homology i)
    (y : (Cosimplicial.ModuleComplex.complex (CechCup.cochainAlgebra fY n FY)).homology j) :
    HomologicalComplex.homologyMap (complexMap g hg n FX FY ρ α) (i + j)
      (Cosimplicial.ModuleCup.cohomologyCup _ i j x y) =
        Cosimplicial.ModuleCup.cohomologyCup _ i j
          (HomologicalComplex.homologyMap (complexMap g hg n FX FY ρ α) i x)
          (HomologicalComplex.homologyMap (complexMap g hg n FX FY ρ α) j y) :=
  Cosimplicial.ModuleCup.cohomologyCup_natural (CupRefinement.map g hg n FX FY ρ α) i j x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CupRefinement
