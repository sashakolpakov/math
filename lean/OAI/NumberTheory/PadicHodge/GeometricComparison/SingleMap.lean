import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Linear
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Single Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SingleMap.SingleMapCycles

noncomputable section

/-! Actual maps from a single complex are exactly cycles in the linear Hom complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [Linear R C] (A : C) (K : CochainComplex C ℤ) (n : ℤ)

def cycles : Submodule R (A ⟶ K.X n) := (Linear.rightComp R A (K.d n (n + 1))).ker

def evaluate : ((HomologicalComplex.single C (.up ℤ) n).obj A ⟶ K) →ₗ[R] cycles R A K n where
  toFun f := ⟨(HomologicalComplex.singleObjXSelf (.up ℤ) n A).inv ≫ f.f n, by
    change ((HomologicalComplex.singleObjXSelf (.up ℤ) n A).inv ≫ f.f n) ≫ K.d n (n + 1) = 0
    rw [Category.assoc, f.comm]
    simp⟩
  map_add' f g := by apply Subtype.ext; simp
  map_smul' r f := by apply Subtype.ext; simp

theorem evaluate_injective : Function.Injective (evaluate R A K n) := by
  intro f g h
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = n
  · subst i
    apply (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) n A).inv).mp
    exact congrArg Subtype.val h
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) n A i hi).eq_of_src _ _

theorem evaluate_surjective : Function.Surjective (evaluate R A K n) := by
  intro x
  let f := HomologicalComplex.mkHomFromSingle (K := K) (j := n) x.val (fun k hk => by
    change n + 1 = k at hk
    subst k
    exact x.property)
  refine ⟨f, Subtype.ext ?_⟩
  change (HomologicalComplex.singleObjXSelf (.up ℤ) n A).inv ≫ f.f n = x.val
  rw [HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]

def equiv : ((HomologicalComplex.single C (.up ℤ) n).obj A ⟶ K) ≃ₗ[R] cycles R A K n :=
  LinearEquiv.ofBijective (evaluate R A K n)
    ⟨evaluate_injective R A K n, evaluate_surjective R A K n⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SingleMap.SingleMapCycles
