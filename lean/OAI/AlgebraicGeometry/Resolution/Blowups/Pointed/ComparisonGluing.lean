import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CenterDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafUniqueness

/-! # Comparison Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ComparisonGluing.Construction

noncomputable section

/-! Global center gluing from pointed comparisons of the actual local ideals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- Equality of ideals can be checked on flat comparison charts through
each closed point. Different charts and different comparison maps may be
used at different points. -/
theorem ideal_eq_of_pointed_flat_comparisons {R : Type u} [CommRing R] (I L : Ideal R)
    (h : ∀ (q : Ideal R) (_ : q.IsMaximal),
      ∃ (S : Type u) (_ : CommRing S), ∃ f g : R →+* S,
        ∃ (Q : Ideal S) (_ : Q.IsPrime), f.Flat ∧ Q.comap f = q ∧
          I.map f = L.map g ∧ L.map f = L.map g) : I = L := by
  apply Ideal.eq_of_localization_maximal
  intro q hq
  let : q.IsMaximal := hq
  obtain ⟨S, instS, f, g, Q, hQ, hf, hqQ, hIL, hLL⟩ := h q hq
  let : CommRing S := instS
  let : Q.IsPrime := hQ
  exact Etale.CenterDescent.Construction.flat_map_ideal_equality_at_prime f hf I L q Q hqQ (hIL.trans hLL.symm)

/-- Pointed flat comparisons on affine opens identify the actual ideal
sheaves, so their closed subschemes agree, including their scheme structures. -/
theorem idealSheaf_eq_of_pointed_flat_comparisons {X : Scheme.{u}}
    (I L : X.IdealSheafData)
    (h : ∀ W : X.affineOpens, ∀ (q : Ideal Γ(X, W)) (_ : q.IsMaximal),
      ∃ (S : Type u) (_ : CommRing S), ∃ f g : Γ(X, W) →+* S,
        ∃ (Q : Ideal S) (_ : Q.IsPrime), f.Flat ∧ Q.comap f = q ∧
          (I.ideal W).map f = (L.ideal W).map g ∧
          (L.ideal W).map f = (L.ideal W).map g) : I = L := by
  ext1
  funext W
  exact ideal_eq_of_pointed_flat_comparisons (I.ideal W) (L.ideal W) (h W)

/-- Compatible pointwise comparisons on the pairwise overlaps of a finite
affine cover construct a unique global ideal sheaf. Pairwise equality of the
local ideal sheaves is proved by flat descent, rather than assumed. -/
theorem existsUnique_idealSheaf_of_pointed_flat_overlap_comparisons
    {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    [∀ i, IsAffine (U i)] [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (hcover : ⨆ i, (j i).opensRange = ⊤) (J : ∀ i, (U i).IdealSheafData)
    (h : ∀ a b : ι, ∀ W : (pullback (j a) (j b)).affineOpens,
      ∀ (q : Ideal Γ(pullback (j a) (j b), W)) (_ : q.IsMaximal),
      ∃ (S : Type u) (_ : CommRing S), ∃ f g : Γ(pullback (j a) (j b), W) →+* S,
        ∃ (Q : Ideal S) (_ : Q.IsPrime), f.Flat ∧ Q.comap f = q ∧
          (((J a).comap (pullback.fst (j a) (j b))).ideal W).map f =
            (((J b).comap (pullback.snd (j a) (j b))).ideal W).map g ∧
          (((J b).comap (pullback.snd (j a) (j b))).ideal W).map f =
            (((J b).comap (pullback.snd (j a) (j b))).ideal W).map g) :
    ∃! I : X.IdealSheafData, ∀ a, I.comap (j a) = J a := by
  apply Blowups.Finite.OpenIdealSheafUniqueness.Construction.existsUnique_idealSheaf_of_finite_affine_cover U j hcover J
  intro a b
  exact idealSheaf_eq_of_pointed_flat_comparisons _ _ (h a b)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ComparisonGluing.Construction
