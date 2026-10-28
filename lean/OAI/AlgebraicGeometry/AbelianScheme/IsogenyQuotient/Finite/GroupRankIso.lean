import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierRank
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Group Rank Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupRankIso.Construction

noncomputable section

/-!
A monomorphism of finite commutative group schemes over a field is an
isomorphism when the actual ranks agree. The argument retains nilpotents:
a finite monomorphism gives a surjection of coordinate algebras, and equal
dimensions make that surjection bijective.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

set_option backward.isDefEq.respectTransparency false in
theorem finiteGroup_mono_isIso_of_finrank_eq
    {k : Type u} [Field k]
    (G H : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X] [IsCommMonObj H.X]
    [IsFinite G.X.hom] [Flat G.X.hom] [IsFinite H.X.hom] [Flat H.X.hom]
    (f : G ⟶ H) [Mono f.hom.hom] (s : Spec (.of k))
    (hr : G.X.hom.finrank s = H.X.hom.finrank s) : IsIso f := by
  obtain ⟨R, hfR, hcR, ⟨eR⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  obtain ⟨T, hfT, hcT, ⟨eT⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k H
  have : Module.Finite k R := hfR
  have : Module.Finite k T := hfT
  have : IsFinite ((hopfSpec (.of k)).obj (.op T)).X.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k T)))
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfT)
  let v := eR.hom ≫ f ≫ eT.inv
  have : Mono v.hom.hom := inferInstanceAs
    (Mono (eR.hom.hom.hom ≫ f.hom.hom ≫ eT.inv.hom.hom))
  have : IsFinite (v.hom.hom.left ≫ ((hopfSpec (.of k)).obj (.op T)).X.hom) := by
    rw [v.hom.hom.w]
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfR)
  have : IsFinite v.hom.hom.left := IsFinite.of_comp _ ((hopfSpec (.of k)).obj (.op T)).X.hom
  have : IsClosedImmersion v.hom.hom.left :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  let a : T ⟶ R := ((hopfSpec.fullyFaithful (R := .of k)).preimage v).unop
  have ha : (hopfSpec (.of k)).map a.op = v := (hopfSpec.fullyFaithful (R := .of k)).map_preimage v
  let ar : CommRingCat.of T ⟶ CommRingCat.of R := CommRingCat.ofHom a.hom.toAlgHom.toRingHom
  have has : Spec.map ar = v.hom.hom.left := congrArg (fun t => t.hom.hom.left) ha
  have : IsClosedImmersion (Spec.map ar) := has.symm ▸ inferInstance
  have hsurj : Function.Surjective a.hom := by
    have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).surjective.comp
      ((IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ar)).2.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of T)).inv).surjective)
    change Function.Surjective
      ((Scheme.ΓSpecIso (.of T)).inv ≫ (Spec.map ar).appTop ≫ (Scheme.ΓSpecIso (.of R)).hom) at hs
    simpa [ar] using hs
  have hdim : Module.finrank k T = Module.finrank k R :=
    (CartierRank.Construction.groupScheme_finrank_of_hopfIso T H eT s).symm.trans
      (hr.symm.trans (CartierRank.Construction.groupScheme_finrank_of_hopfIso R G eR s))
  have hinj : Function.Injective a.hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := a.hom.toLinearMap)).mpr hsurj
  have : IsIso ar := (ConcreteCategory.isIso_iff_bijective ar).mpr ⟨hinj, hsurj⟩
  have : IsIso v.hom.hom.left := has ▸ inferInstanceAs (IsIso (Spec.map ar))
  have : IsIso ((Over.forget _).map v.hom.hom) := inferInstanceAs (IsIso v.hom.hom.left)
  have : IsIso v.hom.hom := isIso_of_reflects_iso v.hom.hom (Over.forget _)
  have : IsIso v := (Grp.mkIso' (asIso v.hom.hom)).isIso_hom
  exact (isIso_comp_left_iff eR.hom (f ≫ eT.inv)).mp this |>
    (isIso_comp_right_iff f eT.inv).mp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupRankIso.Construction
