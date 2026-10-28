import Mathlib

/-! # Finite Flat Retract -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteFlatRetract

noncomputable section

section

/-! The coordinate algebra of a scheme retract of a finite locally free
scheme is finite projective. This is the algebraic flatness step for the
actual projector blocks. -/

theorem finite_projective_algebra_retract
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Projective R A]
    (i : B →ₐ[R] A) (r : A →ₐ[R] B) (h : r.comp i = AlgHom.id R B) :
    Module.Finite R B ∧ Module.Projective R B := by
  have hlinear : r.toLinearMap.comp i.toLinearMap = LinearMap.id :=
    congrArg AlgHom.toLinearMap h
  have hsurj : Function.Surjective r := by
    intro b
    exact ⟨i b, AlgHom.congr_fun h b⟩
  exact ⟨Module.Finite.of_surjective r.toLinearMap hsurj,
    Module.Projective.of_split i.toLinearMap r.toLinearMap hlinear⟩

theorem finite_flat_algebra_retract
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (i : B →ₐ[R] A) (r : A →ₐ[R] B) (h : r.comp i = AlgHom.id R B) :
    Module.Finite R B ∧ Module.Flat R B ∧ Algebra.FinitePresentation R B := by
  let : Module.FinitePresentation R A := Module.FinitePresentation.of_finite_of_finitePresentation R A
  let : Module.Projective R A := Module.Flat.projective_of_finitePresentation
  obtain ⟨hf, hp⟩ := finite_projective_algebra_retract i r h
  let : Module.Finite R B := hf
  let : Module.Projective R B := hp
  let : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  exact ⟨hf, inferInstance, inferInstance⟩

end

/-! Finite affine scheme retracts preserve flatness and finite
presentation. Applied to the coefficient projector this supplies the
relative flatness of a block from that of the ambient torsion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

theorem finite_flat_scheme_retract
    (R : CommRingCat) (G B : Over (Spec R))
    [IsFinite G.hom] [Flat G.hom] [LocallyOfFinitePresentation G.hom]
    [IsFinite B.hom] (i : B ⟶ G) (r : G ⟶ B) (h : i ≫ r = 𝟙 B) :
    Flat B.hom ∧ LocallyOfFinitePresentation B.hom := by
  let : IsAffine G.left := isAffine_of_isAffineHom G.hom
  let : IsAffine B.left := isAffine_of_isAffineHom B.hom
  obtain ⟨AG, ⟨eG⟩⟩ := (essImage_algSpec (R := R) (G := G)).mpr inferInstance
  obtain ⟨AB, ⟨eB⟩⟩ := (essImage_algSpec (R := R) (G := B)).mpr inferInstance
  have : IsIso eG.hom.left := inferInstanceAs
    (IsIso (((Over.forget (Spec R)).mapIso eG).hom))
  have : IsIso eB.inv.left := inferInstanceAs
    (IsIso (((Over.forget (Spec R)).mapIso eB).inv))
  have hAG : IsFinite ((algSpec R).obj AG).hom ∧ Flat ((algSpec R).obj AG).hom ∧
      LocallyOfFinitePresentation ((algSpec R).obj AG).hom := by
    rw [← eG.hom.w]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let : Module.Finite R AG.unop := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff _).mp hAG.1)
  let : Module.Flat R AG.unop := RingHom.flat_algebraMap_iff.mp
    ((Flat.SpecMap_iff).mp hAG.2.1)
  let : Algebra.FinitePresentation R AG.unop := RingHom.finitePresentation_algebraMap.mp
    ((LocallyOfFinitePresentation.SpecMap_iff _).mp hAG.2.2)
  let i' : (algSpec R).obj AB ⟶ (algSpec R).obj AG := eB.hom ≫ i ≫ eG.inv
  let r' : (algSpec R).obj AG ⟶ (algSpec R).obj AB := eG.hom ≫ r ≫ eB.inv
  have h' : i' ≫ r' = 𝟙 _ := by
    dsimp only [i', r']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc i r, h, Category.id_comp, Iso.hom_inv_id]
  let ia : AG.unop ⟶ AB.unop := ((algSpec.fullyFaithful (R := R)).preimage i').unop
  let ra : AB.unop ⟶ AG.unop := ((algSpec.fullyFaithful (R := R)).preimage r').unop
  have ha : ra ≫ ia = 𝟙 AB.unop := by
    have he : (algSpec.fullyFaithful (R := R)).preimage i' ≫
        (algSpec.fullyFaithful (R := R)).preimage r' = 𝟙 AB := by
      apply (algSpec R).map_injective
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
        (algSpec.fullyFaithful (R := R)).map_preimage,
        (algSpec.fullyFaithful (R := R)).map_preimage]
      exact h'
    exact congrArg Quiver.Hom.unop he
  have halg : ia.hom.comp ra.hom = AlgHom.id R AB.unop :=
    congrArg CommAlgCat.Hom.hom ha
  obtain ⟨hf, hflat, hfp⟩ := finite_flat_algebra_retract ra.hom ia.hom halg
  let : Module.Finite R AB.unop := hf
  let : Module.Flat R AB.unop := hflat
  let : Algebra.FinitePresentation R AB.unop := hfp
  have : Flat ((algSpec R).obj AB).hom := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap R AB.unop)))
    exact (Flat.SpecMap_iff).mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  have : LocallyOfFinitePresentation ((algSpec R).obj AB).hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R AB.unop)))
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr hfp)
  rw [← eB.inv.w]
  exact ⟨inferInstance, inferInstance⟩

/-- The affine retraction argument applies over an arbitrary base by its
actual affine open cover and canonical pullback maps. -/
theorem finite_flat_scheme_retract_general
    {S : Scheme} (G B : Over S)
    [IsFinite G.hom] [Flat G.hom] [LocallyOfFinitePresentation G.hom]
    [IsFinite B.hom] (i : B ⟶ G) (r : G ⟶ B) (h : i ≫ r = 𝟙 B) :
    Flat B.hom ∧ LocallyOfFinitePresentation B.hom := by
  let : IsZariskiLocalAtTarget (@Flat) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ Flat.instHasRingHomPropertyFlat
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _
      instHasRingHomPropertyLocallyOfFinitePresentationFinitePresentation
  let U := S.affineOpenCover
  have hlocal (a : U.I₀) :
      Flat ((Over.pullback (U.f a)).obj B).hom ∧
        LocallyOfFinitePresentation ((Over.pullback (U.f a)).obj B).hom := by
    let F := Over.pullback (U.f a)
    have : IsFinite (F.obj G).hom := inferInstanceAs
      (IsFinite (Limits.pullback.snd G.hom (U.f a)))
    have : Flat (F.obj G).hom := inferInstanceAs (Flat (Limits.pullback.snd G.hom (U.f a)))
    have : LocallyOfFinitePresentation (F.obj G).hom := inferInstanceAs
      (LocallyOfFinitePresentation (Limits.pullback.snd G.hom (U.f a)))
    have : IsFinite (F.obj B).hom := inferInstanceAs
      (IsFinite (Limits.pullback.snd B.hom (U.f a)))
    exact finite_flat_scheme_retract (U.X a) (F.obj G) (F.obj B) (F.map i) (F.map r)
      (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id])
  exact ⟨IsZariskiLocalAtTarget.of_openCover (P := @Flat) U.openCover (fun a => (hlocal a).1),
    IsZariskiLocalAtTarget.of_openCover (P := @LocallyOfFinitePresentation) U.openCover
      (fun a => (hlocal a).2)⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteFlatRetract
