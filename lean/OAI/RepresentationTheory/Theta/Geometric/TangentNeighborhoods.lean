import OAI.RepresentationTheory.Theta.Geometric.Affine.Tangents
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

/-! # Tangent Neighborhoods -/

namespace OAI.RepresentationTheory.Theta.Geometric.TangentNeighborhoods

noncomputable section

/-! Dual-number points based in an open subscheme factor uniquely through
that same neighborhood. The infinitesimal spectrum has one actual point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem dualNumberPrime_mem {k : Type u} [Field k] (p : PrimeSpectrum (DualNumber k))
    (a : DualNumber k) : a ∈ p.asIdeal ↔ a.fst = 0 := by
  constructor
  · intro ha
    by_contra hn
    have hu : IsUnit a := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hn)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal ha hu)
  · intro ha
    have hz : a * a = 0 := by
      apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha]
    exact (p.isPrime.mem_or_mem (hz ▸ p.asIdeal.zero_mem)).elim id id

theorem dualNumberSpectrum_subsingleton (k : Type u) [Field k] :
    Subsingleton (PrimeSpectrum (DualNumber k)) := by
  constructor
  intro p q
  apply PrimeSpectrum.ext
  ext a
  rw [dualNumberPrime_mem, dualNumberPrime_mem]

theorem dualNumberOrigin_surjective (k : Type u) [Field k] :
    Function.Surjective (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k).left := by
  let : Subsingleton (PrimeSpectrum (DualNumber k)) := dualNumberSpectrum_subsingleton k
  change Function.Surjective (PrimeSpectrum.comap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k))
  intro p
  exact ⟨⟨⊥, inferInstance⟩, Subsingleton.elim _ _⟩

variable {B : Scheme.{u}} {T T₀ X U : Over B} (t : T₀ ⟶ T)
  (ht : Function.Surjective t.left) (i : U ⟶ X) [IsOpenImmersion i.left]
  (p : T₀ ⟶ U)

include ht

omit [IsOpenImmersion i.left] in
theorem tangentNeighborhood_range (f : T ⟶ X) (hf : t ≫ f = p ≫ i) :
    Set.range f.left ⊆ Set.range i.left := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, rfl⟩ := ht y
  have he := congrArg (fun h : T₀ ⟶ X => h.left z) hf
  exact ⟨p.left z, he.symm⟩

def tangentNeighborhoodLift (f : T ⟶ X) (hf : t ≫ f = p ≫ i) : T ⟶ U :=
  Over.homMk (IsOpenImmersion.lift i.left f.left (tangentNeighborhood_range t ht i p f hf)) (by
    rw [← i.w, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact f.w)

theorem tangentNeighborhoodLift_fac (f : T ⟶ X) (hf : t ≫ f = p ≫ i) :
    tangentNeighborhoodLift t ht i p f hf ≫ i = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

theorem tangentNeighborhoodLift_origin (f : T ⟶ X) (hf : t ≫ f = p ≫ i) :
    t ≫ tangentNeighborhoodLift t ht i p f hf = p := by
  apply Over.OverMorphism.ext
  apply (cancel_mono i.left).mp
  change (t.left ≫ (tangentNeighborhoodLift t ht i p f hf).left) ≫ i.left = p.left ≫ i.left
  rw [Category.assoc]
  exact (congrArg (fun h : T ⟶ X => t.left ≫ h.left)
    (tangentNeighborhoodLift_fac t ht i p f hf)).trans (congrArg Over.Hom.left hf)

def tangentNeighborhoodEquiv :
    {f : T ⟶ U // t ≫ f = p} ≃ {f : T ⟶ X // t ≫ f = p ≫ i} where
  toFun f := ⟨f.val ≫ i, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ i) f.property)⟩
  invFun f := ⟨tangentNeighborhoodLift t ht i p f.val f.property,
    tangentNeighborhoodLift_origin t ht i p f.val f.property⟩
  left_inv f := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    apply (cancel_mono i.left).mp
    exact congrArg Over.Hom.left (tangentNeighborhoodLift_fac t ht i p (f.val ≫ i)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ i) f.property)))
  right_inv f := Subtype.ext (tangentNeighborhoodLift_fac t ht i p f.val f.property)

end

end OAI.RepresentationTheory.Theta.Geometric.TangentNeighborhoods
