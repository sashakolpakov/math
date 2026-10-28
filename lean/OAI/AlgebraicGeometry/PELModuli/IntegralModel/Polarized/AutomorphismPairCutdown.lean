import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.EndomorphismEquationLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismEquationCriterion
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismRestriction

/-! # Automorphism Pair Cutdown -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismPairCutdown

noncomputable section

section

/-! Impose the actual polarized full-level automorphism condition on an
inverse-pair ambient. The cutdown carries a universal polarized automorphism
and retains every such automorphism on every reduced test. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem exists_reduced_relative_polarized_automorphism_cutdown
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (Z : Over S) [IsReduced Z.left] [IsNoetherian Z.left]
    (r s : Finite.Actions.GroupEndRing (A.abelian.pullback Z.hom)) (hrs : r * s = 1) (hsr : s * r = 1) :
    ∃ (W : Over S) (j : W ⟶ Z), IsReduced W.left ∧ IsClosedImmersion j.left ∧
      ∃ u : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback W.hom) (A.pullback W.hom),
        Finite.Actions.GroupEndRing.ofHom _ u.abelian.hom = EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian j r ∧
        ∀ (T : Over S) [IsReduced T.left] (f : T ⟶ Z)
          (eT : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)),
          EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f r = Finite.Actions.GroupEndRing.ofHom _ eT.abelian.hom →
            ∃! c : T ⟶ W, c ≫ j = f := by
  let B := A.pullback Z.hom
  let e := Finite.Actions.GroupEndRing.inversePairIso B.abelian r s hrs hsr
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom (r.hom B.abelian))
  let d := DualPicardAutomorphism.inverseDualAutomorphism B.dual e
  have : IsMonHom d.hom := DualPicardAutomorphism.inverseDualAutomorphism_isMonHom B.dual e
  have hP := DualPicardAutomorphism.inverseDualAutomorphism_poincare B.dual e
  obtain ⟨C, hr, hc, uC, he, _, hclass⟩ :=
    AutomorphismEquationCriterion.exists_reduced_fixed_polarized_automorphism_locus B e d hP
  let W : Over S := Over.mk (C.hom ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk C.hom rfl
  let u := AutomorphismRestriction.flattenPolarizedAutomorphism A j uC
  have hu : Finite.Actions.GroupEndRing.ofHom _ u.abelian.hom = EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian j r := by
    apply Finite.Actions.GroupEndRing.ext
    apply AutomorphismRestriction.flattenPolarizedAutomorphism_hom A j uC r
    exact congrArg Iso.hom he
  refine ⟨W, j, hr, hc, u, hu, ?_⟩
  intro T _ f eT hf
  let t : Over Z.left := Over.mk f.left
  have : IsReduced t.left := inferInstanceAs (IsReduced T.left)
  let v := AutomorphismRestriction.liftPolarizedAutomorphism A f eT
  have hv : v.abelian = (Over.pullback f.left).mapIso e :=
    Iso.ext (AutomorphismRestriction.liftPolarizedAutomorphism_hom A f eT r hf)
  have hfixed := AutomorphismEquationCriterion.fixed_polarized_automorphism_equations_of_iso B e d hP f.left v hv
  exact (OverLocusClassification.over_existsUnique_lift_iff j f).mpr
    ((UniqueOverHom.unique_over_hom_iff t C).mp ((hclass t).mp hfixed))

end

/-! A bounded pair of endomorphisms is cut down to actual polarized
automorphisms, imposing inverse, polarization, and level equations.
Every polarized automorphism with this pair lifts uniquely to the cutdown. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_reduced_polarized_automorphism_pair_cutdown
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (Z : Over S) [IsNoetherian Z.left] (r s : Finite.Actions.GroupEndRing (A.abelian.pullback Z.hom)) :
    ∃ (W : Over S) (j : W ⟶ Z), IsReduced W.left ∧ IsClosedImmersion j.left ∧
      ∃ u : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback W.hom) (A.pullback W.hom),
        Finite.Actions.GroupEndRing.ofHom _ u.abelian.hom = EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian j r ∧
        ∀ (T : Over S) [IsReduced T.left] (f : T ⟶ Z)
          (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)),
          EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f r = Finite.Actions.GroupEndRing.ofHom _ e.abelian.hom →
          EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f s = Finite.Actions.GroupEndRing.ofHom _ e.abelian.inv →
            ∃! c : T ⟶ W, c ≫ j = f := by
  obtain ⟨V, a, hv, ha, hinv, hV⟩ := Relative.EndomorphismEquationLocus.exists_reduced_relative_inverse_pair_locus A.abelian Z r s
  have : IsReduced V.left := hv
  have : IsClosedImmersion a.left := ha
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian a.left
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace a.left
  have : IsNoetherian V.left := ⟨⟩
  obtain ⟨W, b, hw, hb, u, hu, hW⟩ := exists_reduced_relative_polarized_automorphism_cutdown A V
    (EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian a r) (EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian a s) hinv.1 hinv.2
  have : IsClosedImmersion b.left := hb
  let j := b ≫ a
  have : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (b.left ≫ a.left))
  have : Mono j := Over.mono_of_mono_left j
  refine ⟨W, j, hw, inferInstance, u, hu.trans (EndomorphismFamiliesId.EndomorphismFamilies.restrict_comp A.abelian b a r).symm, ?_⟩
  intro T _ f e hf hs
  have he : EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f r * EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f s = 1 ∧
      EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f s * EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f r = 1 := by
    rw [hf, hs]
    constructor <;> apply Finite.Actions.GroupEndRing.ext
    · exact e.abelian.inv_hom_id
    · exact e.abelian.hom_inv_id
  obtain ⟨c, hc, _⟩ := (hV T f).mp he
  have hc' : EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian c (EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian a r) = Finite.Actions.GroupEndRing.ofHom _ e.abelian.hom := by
    rw [← EndomorphismFamiliesId.EndomorphismFamilies.restrict_comp, hc]
    exact hf
  obtain ⟨k, hk, _⟩ := hW T c e hc'
  have hk' : k ≫ j = f := (Category.assoc k b a).symm.trans
    ((congrArg (fun m => m ≫ a) hk).trans hc)
  exact ⟨k, hk', fun k' hk'₁ => (cancel_mono j).mp (hk'₁.trans hk'.symm)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismPairCutdown
