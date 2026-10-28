import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupBoundaries
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Module Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleComplex

noncomputable section

/-! The original alternating-coface complex of a cosimplicial algebra,
retaining its coefficient-module structure. Its differential and cup
operations agree with those of the underlying cosimplicial ring. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

universe u v

variable {R : Type u} [CommRing R] (A : CosimplicialObject (CommAlgCat.{v} R))

def ringObject : CosimplicialObject CommRingCat.{v} :=
  A ⋙ forget₂ (CommAlgCat R) CommRingCat

instance ringObject_algebra (n : SimplexCategory) : Algebra R ((ringObject A).obj n) :=
  inferInstanceAs (Algebra R (A.obj n))

def moduleObject : CosimplicialObject (ModuleCat.{v} R) :=
  A ⋙ forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)

def complex : CochainComplex (ModuleCat.{v} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).obj (moduleObject A)

theorem complex_d_apply (n : ℕ) (x : A.obj ⦋n⦌) :
    (complex A).d n (n + 1) x = Cup.differential (ringObject A) n x := by
  dsimp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  let ev : ((moduleObject A).obj ⦋n⦌ ⟶ (moduleObject A).obj ⦋n + 1⦌) →+
      (moduleObject A).obj ⦋n + 1⦌ :=
    { toFun := fun f => f x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val • (moduleObject A).δ i) Finset.univ

theorem d_apply_eq_additive (m n : ℕ) (x : A.obj ⦋m⦌) :
    (complex A).d m n x = (Cup.complex (ringObject A)).d m n x := by
  by_cases h : m + 1 = n
  · subst n
    exact (complex_d_apply A m x).trans (Cup.complex_d_apply (ringObject A) m x).symm
  · rw [(complex A).shape m n h, (Cup.complex (ringObject A)).shape m n h]
    rfl

theorem cycle_differential {n : ℕ} (x : Module.CochainClasses.cycles (complex A) n) :
    Cup.differential (ringObject A) n x.1 = 0 :=
  (complex_d_apply A n x.1).symm.trans x.2

def additiveCycle {n : ℕ} (x : Module.CochainClasses.cycles (complex A) n) :
    Additive.CohomologyRepresentatives.cocycles (Cup.complex (ringObject A)) n :=
  ⟨x.1, (Additive.CohomologyRepresentatives.mem_cocycles_iff
    (Cup.complex (ringObject A)) n x.1).mpr
    ((Cup.complex_d_apply (ringObject A) n x.1).trans (cycle_differential A x))⟩

theorem boundary_iff_additive (n : ℕ) (x : A.obj ⦋n⦌) :
    (∃ b : (complex A).X ((ComplexShape.up ℕ).prev n),
      (complex A).d ((ComplexShape.up ℕ).prev n) n b = x) ↔
    ∃ b : ((Cup.complex (ringObject A)).sc n).X₁,
      ((Cup.complex (ringObject A)).sc n).f b = x := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (d_apply_eq_additive A _ n b).symm.trans hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (d_apply_eq_additive A _ n b).trans hb⟩

theorem cup_smul_left {p q : ℕ} (r : R) (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) :
    Cup.cup (ringObject A) (r • x) y =
      r • (Cup.cup (ringObject A) x y : A.obj ⦋p + q⦌) := by
  change (A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q)).hom (r • x) *
      (A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q)).hom y =
    r • ((A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q)).hom x *
      (A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q)).hom y)
  rw [map_smul, smul_mul_assoc]

theorem cup_smul_right {p q : ℕ} (r : R) (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) :
    Cup.cup (ringObject A) x (r • y) =
      r • (Cup.cup (ringObject A) x y : A.obj ⦋p + q⦌) := by
  change (A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q)).hom x *
      (A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q)).hom (r • y) =
    r • ((A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q)).hom x *
      (A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q)).hom y)
  rw [map_smul, mul_smul_comm]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleComplex
