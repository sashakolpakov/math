import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientEqualities

/-! # Base Change Map Equality -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.BaseChangeMapEquality.Abelian

noncomputable section

/-! Exact comparison of base-changed morphism equations with the coefficient family diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem over_baseChange_map_eq_iff
    {S S' : Scheme} (q : S' ⟶ S) {A B : Over S} (a b : A ⟶ B) :
    (Over.pullback q).map a = (Over.pullback q).map b ↔
      pullback.snd q A.hom ≫ a.left = pullback.snd q A.hom ≫ b.left := by
  constructor
  · intro h
    have h' := congrArg (fun u : (Over.pullback q).obj A ⟶ (Over.pullback q).obj B =>
      u.left ≫ pullback.fst B.hom q) h
    simp only [Over.pullback_map_left, pullback.lift_fst] at h'
    have h'' := congrArg (fun u => (pullbackSymmetry q A.hom).hom ≫ u) h'
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst] using h''
  · intro h
    have h' := congrArg (fun u => (pullbackSymmetry A.hom q).hom ≫ u) h
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_snd] at h'
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.pullback_map_left, pullback.lift_fst] using h'
    · simp only [Over.pullback_map_left, pullback.lift_snd]

theorem over_morphism_equality_descends_to_finite_coefficients
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    {X Y : Over (Spec (CommRingCat.of R))} [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    (a b : X ⟶ Y)
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map a =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map b) :
    ∃ s : (Finset B)ᵒᵖ,
      (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).map a =
        (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).map b := by
  obtain ⟨s, hs⟩ := FiniteCoefficientEqualities.Abelian.family_morphism_equality_descends_to_finite_coefficients R B X.hom Y.hom
    a.left b.left a.w b.w ((over_baseChange_map_eq_iff _ a b).mp h)
  refine ⟨s, (over_baseChange_map_eq_iff _ a b).mpr ?_⟩
  exact hs

end

end OAI.ArithmeticGeometry.Descent.CMVariety.BaseChangeMapEquality.Abelian
