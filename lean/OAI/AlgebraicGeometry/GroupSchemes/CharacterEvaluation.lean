import OAI.AlgebraicGeometry.GroupSchemes.LikeCharacters
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-! # Character Evaluation -/

namespace OAI.AlgebraicGeometry.GroupSchemes.CharacterEvaluation.FiniteEtale

noncomputable section

/-! A basis of grouplike characters identifies all affine points by evaluation. -/

open WithConv

universe u
variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A]

/-- When grouplike elements span, the group algebra on them is the coordinate algebra. -/
def groupAlgebraEquiv
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤) :
    MonoidAlgebra k (GroupLike k A) ≃ₐ[k] A := by
  let q := MonoidAlgebra.lift k A (GroupLike k A) (GroupLike.valMonoidHom k A)
  have hq : (q : MonoidAlgebra k (GroupLike k A) → A) =
      (Finsupp.linearCombination k GroupLike.val) ∘ MonoidAlgebra.coeff := by
    funext x
    simp only [q, MonoidAlgebra.lift_apply, Finsupp.linearCombination_apply,
      Function.comp_apply, GroupLike.valMonoidHom_apply]
  apply AlgEquiv.ofBijective q
  rw [hq]
  exact ⟨linearIndep_groupLikeVal.finsuppLinearCombination_injective.comp
      (MonoidAlgebra.coeffEquiv.injective),
    ((span_range_eq_top_iff_surjective_finsuppLinearCombination k (v := GroupLike.val)).mp hspan).comp
      MonoidAlgebra.coeffEquiv.surjective⟩

/-- The group algebra equivalence sends a group basis element to its coordinate character. -/
theorem groupAlgebraEquiv_single
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤)
    (t : GroupLike k A) : groupAlgebraEquiv k A hspan (MonoidAlgebra.single t 1) = t.val := by
  change MonoidAlgebra.lift k A (GroupLike k A) (GroupLike.valMonoidHom k A)
    (MonoidAlgebra.single t 1) = _
  rw [MonoidAlgebra.lift_single, one_smul]
  rfl

variable (R : Type u) [CommRing R] [Algebra k R]

/-- Algebra maps are exactly homomorphisms from coordinate characters into the target ring. -/
def algHomCharactersEquiv
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤) :
    (A →ₐ[k] R) ≃ (GroupLike k A →* R) :=
  (AlgEquiv.arrowCongr (groupAlgebraEquiv k A hspan).symm (AlgEquiv.refl : R ≃ₐ[k] R)).trans
    (MonoidAlgebra.lift k R (GroupLike k A)).symm

/-- This equivalence is evaluation on each character. -/
theorem algHomCharactersEquiv_apply
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤)
    (f : A →ₐ[k] R) (t : GroupLike k A) :
    algHomCharactersEquiv k A R hspan f t = f t.val := by
  change f (groupAlgebraEquiv k A hspan (MonoidAlgebra.single t 1)) = _
  rw [groupAlgebraEquiv_single]

/-- Character evaluation intertwines the convolution point law with pointwise multiplication. -/
def pointsCharactersEquiv
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤) :
    WithConv (A →ₐ[k] R) ≃* (GroupLike k A →* R) where
  toEquiv := (WithConv.equiv _).trans (algHomCharactersEquiv k A R hspan)
  map_mul' f g := by
    ext t
    change algHomCharactersEquiv k A R hspan (f * g).ofConv t =
      algHomCharactersEquiv k A R hspan f.ofConv t *
        algHomCharactersEquiv k A R hspan g.ofConv t
    rw [algHomCharactersEquiv_apply, algHomCharactersEquiv_apply,
      algHomCharactersEquiv_apply, AlgHom.convMul_apply,
      t.isGroupLikeElem_val.comul_eq_tmul_self]
    simp

/-- A homomorphism from a cyclic group is determined by an arbitrary root of unity. -/
def cyclicHomRootsEquiv {C : Type u} [CommGroup C] (t : C) (N : ℕ)
    (hgen : ∀ x : C, x ∈ Subgroup.zpowers t) (horder : orderOf t = N) :
    (C →* Rˣ) ≃* rootsOfUnity N R where
  toFun f := ⟨f t, by
    change f t ^ N = 1
    rw [← map_pow, ← horder, pow_orderOf_eq_one, map_one]⟩
  invFun x := monoidHomOfForallMemZpowers hgen
    (by rw [horder]; exact orderOf_dvd_of_pow_eq_one x.property)
  left_inv f := by
    apply (MonoidHom.eq_iff_eq_on_generator hgen _ _).mpr
    exact monoidHomOfForallMemZpowers_apply_gen _ _
  right_inv x := by
    apply Subtype.ext
    exact monoidHomOfForallMemZpowers_apply_gen _ _
  map_mul' f g := rfl

/-- A cyclic basis of grouplike characters identifies all affine points with roots of unity. -/
def pointsRootsEquiv
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤)
    (t : GroupLike k A) (N : ℕ) (hgen : ∀ x : GroupLike k A, x ∈ Subgroup.zpowers t)
    (horder : orderOf t = N) : WithConv (A →ₐ[k] R) ≃* rootsOfUnity N R :=
  ((pointsCharactersEquiv k A R hspan).trans MonoidHom.toHomUnitsMulEquiv).trans
    (cyclicHomRootsEquiv R t N hgen horder)

/-- The resulting root has underlying ring element obtained by evaluating the generator. -/
theorem pointsRootsEquiv_apply
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤)
    (t : GroupLike k A) (N : ℕ) (hgen : ∀ x : GroupLike k A, x ∈ Subgroup.zpowers t)
    (horder : orderOf t = N) (f : WithConv (A →ₐ[k] R)) :
    ((pointsRootsEquiv k A R hspan t N hgen horder f).val : R) = f.ofConv t.val :=
  algHomCharactersEquiv_apply k A R hspan f.ofConv t

end

end OAI.AlgebraicGeometry.GroupSchemes.CharacterEvaluation.FiniteEtale
