import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismFamiliesId
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniqueOverHom
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverLocusClassification

/-! # Endomorphism Equation Locus -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Relative.EndomorphismEquationLocus

/-! Equations between actual endomorphism-family values have reduced
closed loci, with factorization expressed using the original base and
the actual canonical restriction maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem restrict_groupEnd_eq_iff {T U : Over S} (f : T ⟶ U)
    (r s : Finite.Actions.GroupEndRing (A.pullback U.hom)) :
    EndomorphismFamiliesId.EndomorphismFamilies.restrict A f r = EndomorphismFamiliesId.EndomorphismFamilies.restrict A f s ↔
      (Over.pullback f.left).map (r.hom (A.pullback U.hom)) =
        (Over.pullback f.left).map (s.hom (A.pullback U.hom)) := by
  constructor
  · intro h
    have he := congrArg (Finite.Actions.GroupEndRing.hom (A.pullback T.hom)) h
    change (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).inv ≫ (Over.pullback f.left).map (r.hom (A.pullback U.hom)) ≫
      (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).hom =
      (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).inv ≫ (Over.pullback f.left).map (s.hom (A.pullback U.hom)) ≫
        (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).hom at he
    exact (cancel_mono (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).hom).mp ((cancel_epi (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).inv).mp he)
  · intro h
    apply Finite.Actions.GroupEndRing.ext
    change (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).inv ≫ (Over.pullback f.left).map (r.hom (A.pullback U.hom)) ≫
      (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).hom =
      (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).inv ≫ (Over.pullback f.left).map (s.hom (A.pullback U.hom)) ≫
        (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).hom
    rw [h]

theorem exists_reduced_relative_endomorphism_equation_locus
    (Z : Over S) [IsLocallyNoetherian Z.left] {I : Type}
    (r s : I → Finite.Actions.GroupEndRing (A.pullback Z.hom)) :
    ∃ (W : Over S) (j : W ⟶ Z), IsReduced W.left ∧ IsClosedImmersion j.left ∧
      (∀ i, EndomorphismFamiliesId.EndomorphismFamilies.restrict A j (r i) = EndomorphismFamiliesId.EndomorphismFamilies.restrict A j (s i)) ∧
      ∀ (T : Over S) [IsReduced T.left] (f : T ⟶ Z),
        (∀ i, EndomorphismFamiliesId.EndomorphismFamilies.restrict A f (r i) = EndomorphismFamiliesId.EndomorphismFamilies.restrict A f (s i)) ↔
          ∃! c : T ⟶ W, c ≫ j = f := by
  obtain ⟨C, hr, hc, _, hC⟩ := SmoothEquationLocus.exists_reduced_smooth_equation_locus
    (fun i => (r i).hom (A.pullback Z.hom)) (fun i => (s i).hom (A.pullback Z.hom))
  let W : Over S := Over.mk (C.hom ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk C.hom rfl
  have : IsReduced W.left := hr
  have : IsClosedImmersion j.left := hc
  have : Mono j := Over.mono_of_mono_left j
  have hclass (T : Over S) [IsReduced T.left] (f : T ⟶ Z) :
      (∀ i, EndomorphismFamiliesId.EndomorphismFamilies.restrict A f (r i) = EndomorphismFamiliesId.EndomorphismFamilies.restrict A f (s i)) ↔
        ∃! c : T ⟶ W, c ≫ j = f := by
    let t : Over Z.left := Over.mk f.left
    have : IsReduced t.left := inferInstanceAs (IsReduced T.left)
    exact (forall_congr' (fun i => restrict_groupEnd_eq_iff A f (r i) (s i))).trans
      ((hC t).trans ((UniqueOverHom.unique_over_hom_iff t C).trans (OverLocusClassification.over_existsUnique_lift_iff j f).symm))
  refine ⟨W, j, hr, hc, (hclass W j).mpr ?_, hclass⟩
  refine ⟨𝟙 W, Category.id_comp j, fun c hc => ?_⟩
  exact (cancel_mono j).mp (hc.trans (Category.id_comp j).symm)

end AlgebraicGeometry.PELModuli.IntegralModel.Relative.EndomorphismEquationLocus

namespace AlgebraicGeometry.PELModuli.IntegralModel

/-! Inverse endomorphism pairs form an actual reduced closed locus in
any endomorphism ambient. Their universal inverse equations give the
group-scheme automorphism itself. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g : ℕ}

def Finite.Actions.GroupEndRing.inversePairIso (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f h : Finite.Actions.GroupEndRing A)
    (hfh : f * h = 1) (hhf : h * f = 1) : A.scheme ≅ A.scheme where
  hom := f.hom A
  inv := h.hom A
  hom_inv_id := congrArg (Finite.Actions.GroupEndRing.hom A) hhf
  inv_hom_id := congrArg (Finite.Actions.GroupEndRing.hom A) hfh

theorem Relative.EndomorphismEquationLocus.exists_reduced_relative_inverse_pair_locus (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (Z : Over S) [IsLocallyNoetherian Z.left]
    (f h : Finite.Actions.GroupEndRing (A.pullback Z.hom)) :
    ∃ (W : Over S) (j : W ⟶ Z), IsReduced W.left ∧ IsClosedImmersion j.left ∧
      (EndomorphismFamiliesId.EndomorphismFamilies.restrict A j f * EndomorphismFamiliesId.EndomorphismFamilies.restrict A j h = 1 ∧ EndomorphismFamiliesId.EndomorphismFamilies.restrict A j h * EndomorphismFamiliesId.EndomorphismFamilies.restrict A j f = 1) ∧
      ∀ (T : Over S) [IsReduced T.left] (c : T ⟶ Z),
        (EndomorphismFamiliesId.EndomorphismFamilies.restrict A c f * EndomorphismFamiliesId.EndomorphismFamilies.restrict A c h = 1 ∧ EndomorphismFamiliesId.EndomorphismFamilies.restrict A c h * EndomorphismFamiliesId.EndomorphismFamilies.restrict A c f = 1) ↔
          ∃! k : T ⟶ W, k ≫ j = c := by
  let r : Bool → Finite.Actions.GroupEndRing (A.pullback Z.hom) := fun b => if b then f * h else h * f
  obtain ⟨W, j, hr, hc, hU, hclass⟩ :=
    Relative.EndomorphismEquationLocus.exists_reduced_relative_endomorphism_equation_locus A Z r (fun _ => 1)
  have hi (T : Over S) (c : T ⟶ Z) :
      (∀ b, EndomorphismFamiliesId.EndomorphismFamilies.restrict A c (r b) = EndomorphismFamiliesId.EndomorphismFamilies.restrict A c 1) ↔
        (EndomorphismFamiliesId.EndomorphismFamilies.restrict A c f * EndomorphismFamiliesId.EndomorphismFamilies.restrict A c h = 1 ∧ EndomorphismFamiliesId.EndomorphismFamilies.restrict A c h * EndomorphismFamiliesId.EndomorphismFamilies.restrict A c f = 1) := by
    constructor
    · intro H
      exact ⟨by simpa only [r, Bool.false_eq_true, ite_false, ite_true, map_mul, map_one] using H true, by simpa only [r, Bool.false_eq_true, ite_false, ite_true, map_mul, map_one] using H false⟩
    · rintro ⟨Hf, Hh⟩ b
      cases b
      · simpa only [r, Bool.false_eq_true, ite_false, ite_true, map_mul, map_one] using Hh
      · simpa only [r, Bool.false_eq_true, ite_false, ite_true, map_mul, map_one] using Hf
  exact ⟨W, j, hr, hc, (hi W j).mp hU,
    fun T _ c => (hi T c).symm.trans (hclass T c)⟩

end AlgebraicGeometry.PELModuli.IntegralModel

end

end OAI
