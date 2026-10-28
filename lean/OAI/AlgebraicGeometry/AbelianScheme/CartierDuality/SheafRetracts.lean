import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRetracts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.CategoryTheory.Idempotents.Basic

/-! # Sheaf Retracts -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: actual finite locally free sheaf direct factors and product blocks
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v

namespace SheafRetracts.Construction.Retracts

/-- Two splittings of the same idempotent are canonically isomorphic. -/
def splittingIso {C : Type u} [Category.{v} C] {X Y Z : C}
    (i : Y ⟶ X) (r : X ⟶ Y) (h : i ≫ r = 𝟙 Y)
    (j : Z ⟶ X) (s : X ⟶ Z) (k : j ≫ s = 𝟙 Z) (p : r ≫ i = s ≫ j) : Y ≅ Z where
  hom := i ≫ s
  inv := j ≫ r
  hom_inv_id := by
    calc
      (i ≫ s) ≫ (j ≫ r) = i ≫ (s ≫ j) ≫ r := by simp only [Category.assoc]
      _ = i ≫ (r ≫ i) ≫ r := by rw [p]
      _ = 𝟙 Y := by simp only [← Category.assoc, h, Category.id_comp]
  inv_hom_id := by
    calc
      (j ≫ r) ≫ (i ≫ s) = j ≫ (r ≫ i) ≫ s := by simp only [Category.assoc]
      _ = j ≫ (s ≫ j) ≫ s := by rw [p]
      _ = 𝟙 Z := by simp only [← Category.assoc, k, Category.id_comp]

/-- A native subgroup of a commutative group is commutative, detected
on every test object by the injective point map. -/
theorem commutative_of_mono {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [BraidedCategory C]
    {G H : Grp C} [IsCommMonObj G.X] (i : H ⟶ G) [Mono i.hom.hom] : IsCommMonObj H.X := by
  apply (isCommMonObj_iff_isMulCommutative H.X).mpr
  intro T
  refine ⟨⟨fun a b => ?_⟩⟩
  apply (cancel_mono i.hom.hom).mp
  simp only [MonObj.mul_comp, mul_comm]

end SheafRetracts.Construction.Retracts

/-- Every sheaf direct factor of a finite locally free commutative
group sheaf is itself represented by a finite locally free group scheme. -/
theorem SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb.of_retract {S : Scheme.{u}} {F K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (hF : SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S F) (i : K ⟶ F) (r : F ⟶ K) (h : i ≫ r = 𝟙 K) :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S K := by
  obtain ⟨G, hc, hf, hflat, hfp, ⟨e⟩⟩ := hF
  let := hc
  let := hf
  let := hflat
  let := hfp
  let a : K ⟶ CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G := i ≫ e.inv
  let b : CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ⟶ K := e.hom ≫ r
  have hab : a ≫ b = 𝟙 K := by simpa [a, b, Category.assoc] using h
  let p : G ⟶ G := (RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G G).symm (b ≫ a)
  have hp : RepresentedMorphisms.Construction.Schemes.representedFppfAbMap p = b ≫ a := (RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G G).apply_symm_apply _
  have hpp : p ≫ p = p := by
    apply (RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv G G).injective
    change RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (p ≫ p) = RepresentedMorphisms.Construction.Schemes.representedFppfAbMap p
    rw [RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp, hp]
    simp only [Category.assoc, ← Category.assoc a b, hab, Category.id_comp]
  let hcpl : IsIdempotentComplete (Grp (Over S)) :=
    (Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent _).mpr
      (fun _ _ _ => inferInstance)
  obtain ⟨Q, j, s, hjs, hsj⟩ := IsIdempotentComplete.idempotents_split G p hpp
  let : Mono j.hom.hom := mono_of_mono_fac (congrArg (fun f => f.hom.hom) hjs)
  let hcQ : IsCommMonObj Q.X := SheafRetracts.Construction.Retracts.commutative_of_mono j
  obtain ⟨hfinQ, hflatQ, hfpQ⟩ := IntrinsicRetracts.Construction.Schemes.finiteLocallyFree_of_retract j s hjs
  let α : CommutativeSheavesAb.Construction.Schemes.representedFppfAb S Q ⟶ CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G := RepresentedMorphisms.Construction.Schemes.representedFppfAbMap j
  let β : CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ⟶ CommutativeSheavesAb.Construction.Schemes.representedFppfAb S Q := RepresentedMorphisms.Construction.Schemes.representedFppfAbMap s
  have hαβ : α ≫ β = 𝟙 (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S Q) :=
    (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp j s).symm.trans
      ((congrArg RepresentedMorphisms.Construction.Schemes.representedFppfAbMap hjs).trans (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_id Q))
  have hβα : β ≫ α = b ≫ a :=
    (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp s j).symm.trans ((congrArg RepresentedMorphisms.Construction.Schemes.representedFppfAbMap hsj).trans hp)
  exact ⟨Q, hcQ, hfinQ, hflatQ, hfpQ, ⟨SheafRetracts.Construction.Retracts.splittingIso α β hαβ a b hab hβα⟩⟩

/-- Every block of an actual product decomposition of a finite locally
free group sheaf is finite locally free representable. -/
theorem SheafBlocks.Construction.Schemes.SheafBlockDecomposition.block_finiteLocallyFree {S : Scheme.{u}} {G : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    {I : Type u} (B : SheafBlocks.Construction.Schemes.SheafBlockDecomposition G I) (hG : SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S G) (i : I) :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (B.block i) :=
  hG.of_retract (B.inclusion i) (B.projection i) (B.inclusion_projection i)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
