import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechDifferential
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality

/-! # Tuple Restriction Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor

noncomputable section

/-! Finite integral tuple matrices act on the original Čech complex of
any presheaf on a preorder. Support containment supplies every restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality

universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category.{w} D] [Preadditive D] [HasProducts.{u} D]
  {ι : Type u} (U : ι → C) (P : Cᵒᵖ ⥤ D)

abbrev complex := NonemptyCechDifferential.complex U P
abbrev factor {n : ℕ} (i : Fin (n + 1) → ι) := P.obj (op (∏ᶜ (U ∘ i)))
abbrev projection {n : ℕ} (i : Fin (n + 1) → ι) :=
  NonemptyCechDifferential.projection U P n i

def inclusion {n m : ℕ} (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) : (∏ᶜ (U ∘ i)) ⟶ ∏ᶜ (U ∘ j) :=
  Pi.lift fun k => Pi.π (U ∘ i) (Classical.choose (h ⟨k, rfl⟩)) ≫
    eqToHom (congrArg U (Classical.choose_spec (h ⟨k, rfl⟩)))

def restriction {n m : ℕ} (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) : factor U P j ⟶ factor U P i :=
  P.map (inclusion U i j h).op

omit [Preadditive D] [HasProducts D] in
theorem restriction_comp {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (k : Fin (l + 1) → ι)
    (hkj : Set.range k ⊆ Set.range j) (hji : Set.range j ⊆ Set.range i) :
    restriction U P j k hkj ≫ restriction U P i j hji =
      restriction U P i k (hkj.trans hji) := by
  rw [restriction, restriction, ← P.map_comp]
  congr 1

omit [Preadditive D] [HasProducts D] in
theorem restriction_self {n : ℕ} (i : Fin (n + 1) → ι) :
    restriction U P i i Set.Subset.rfl = 𝟙 _ := by
  unfold restriction
  rw [Subsingleton.elim (inclusion U i i Set.Subset.rfl) (𝟙 _), op_id, P.map_id]

def rowBasis {n m : ℕ} (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) :
    (complex U P).X m ⟶ factor U P i := by
  classical
  exact if h : Set.range j ⊆ Set.range i then
    projection U P j ≫ restriction U P i j h else 0

theorem rowBasis_of_subset {n m : ℕ} (i : Fin (n + 1) → ι)
    (j : Fin (m + 1) → ι) (h : Set.range j ⊆ Set.range i) :
    rowBasis U P i j = projection U P j ≫ restriction U P i j h := by
  classical
  simp only [rowBasis, dite_eq_left h]

def row {n m : ℕ} (i : Fin (n + 1) → ι) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m →ₗ[ℤ] ((complex U P).X m ⟶ factor U P i) :=
  Finsupp.lsum ℤ fun j => LinearMap.toSpanSingleton ℤ _ (rowBasis U P i j)

theorem row_single {n m : ℕ} (i : Fin (n + 1) → ι)
    (j : Fin (m + 1) → ι) (a : ℤ) :
    row U P i (Finsupp.single j a) = a • rowBasis U P i j := by
  simp only [row, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

theorem row_restriction {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (hji : Set.range j ⊆ Set.range i) (x : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι l)
    (hx : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain.SupportedBy x (Set.range j)) :
    row U P j x ≫ restriction U P i j hji = row U P i x := by
  classical
  simp only [row, Finsupp.lsum_apply, Finsupp.sum, sum_comp,
    LinearMap.toSpanSingleton_apply, zsmul_comp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [rowBasis_of_subset U P j k (hx hk),
    rowBasis_of_subset U P i k ((hx hk).trans hji), Category.assoc,
    restriction_comp]

def map {n m : ℕ} (f : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m)
    (_hf : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) : (complex U P).X m ⟶ (complex U P).X n :=
  Pi.lift fun i => row U P i (f (Finsupp.single i 1))

theorem map_projection {n m : ℕ}
    (f : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m)
    (hf : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) (i : Fin (n + 1) → ι) :
    TupleRestrictionFunctor.map U P f hf ≫ projection U P i = row U P i (f (Finsupp.single i 1)) :=
  Pi.lift_comp_π _ i

theorem map_row {n m l : ℕ}
    (f : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι l)
    (hf : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) (i : Fin (n + 1) → ι)
    (x : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m) (hx : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain.SupportedBy x (Set.range i)) :
    TupleRestrictionFunctor.map U P f hf ≫ row U P i x = row U P i (f x) := by
  classical
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality.linearMap_apply_eq_finsupp_sum_single f x, map_finsuppSum]
  simp only [row, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.toSpanSingleton_apply, comp_sum, comp_zsmul, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rowBasis_of_subset U P i j (hx hj), ← Category.assoc,
    map_projection]
  exact congrArg (fun t => x j • t) (row_restriction U P i j (hx hj)
    (f (Finsupp.single j 1)) (hf j))

theorem map_comp {n m l : ℕ}
    (f : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m)
    (g : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι l)
    (hf : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) (hg : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g) :
    TupleRestrictionFunctor.map U P (g.comp f) (hg.comp hf) = TupleRestrictionFunctor.map U P g hg ≫ TupleRestrictionFunctor.map U P f hf := by
  apply Pi.hom_ext
  intro (i : Fin (n + 1) → ι)
  change _ ≫ projection U P i = _ ≫ projection U P i
  rw [map_projection, Category.assoc, map_projection, map_row]
  · rfl
  · exact hf i

theorem map_boundary (n : ℕ) :
    TupleRestrictionFunctor.map U P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.cechTupleBoundary n) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality.cechTupleBoundary_supportNonincreasing n) =
      (complex U P).d n (n + 1) := by
  apply Pi.hom_ext
  intro (i : Fin (n + 2) → ι)
  change _ ≫ projection U P i = _ ≫ projection U P i
  rw [map_projection, AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.cechTupleBoundary_single, one_smul,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.cechTupleBoundaryBasis, map_sum, NonemptyCechDifferential.differential_projection]
  apply Finset.sum_congr rfl
  intro j _
  have h : Set.range (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.cechTupleDelete i j) ⊆ Set.range i := by
    rintro x ⟨k, rfl⟩
    exact ⟨j.succAbove k, rfl⟩
  rw [row_single, rowBasis_of_subset U P i _ h]
  congr 2

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor
