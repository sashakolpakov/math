import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualBasePullbackProjections

/-! # Base Change Iso Projections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangeIsoProjections

noncomputable section

/-! The existing categorical base-change isomorphism for relative
projective space has the explicit geometric projective base map as its
first projection. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem pullbackComp_inv_fst {S T U : Scheme.{u}} (A : Over S) (f : T ⟶ S) (h : U ⟶ T) :
    ((Over.pullbackComp h f).inv.app A).left ≫ pullback.fst A.hom (h ≫ f) =
      pullback.fst (pullback.snd A.hom f) h ≫ pullback.fst A.hom f :=
  (((Over.forget U).mapIso ((Over.pullbackComp h f).app A)).inv_comp_eq).mpr
    (Pullback.Comparisons.pullbackComp_hom_fst_fst A f h).symm

private theorem projection_chain {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ : C}
    (m : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄)
    (e : A₄ ⟶ B₀) (f : B₀ ⟶ B₁) (z : A₃ ⟶ B₁) (w : A₂ ⟶ B₁)
    (v : A₁ ⟶ B₂) (k : B₂ ⟶ B₁) (u : A₀ ⟶ B₃) (a : B₃ ⟶ B₂) (t : B₃ ⟶ B₁)
    (hd : d ≫ e ≫ f = z) (hc : c ≫ z = w) (hb : b ≫ w = v ≫ k)
    (hm : m ≫ v = u ≫ a) (ha : a ≫ k = t) :
    (m ≫ b ≫ c ≫ d) ≫ e ≫ f = u ≫ t := by
  simp only [Category.assoc] at hd hc hb hm ha ⊢
  rw [hd, hc, hb, ← Category.assoc m v k, hm, Category.assoc, ha]

private def pullbackBaseChangeHom {S T : Scheme.{u}} (f : T ⟶ S)
    (P : Over (Spec Γ(S, ⊤))) (Q : Over (Spec Γ(T, ⊤)))
    (a : Q ≅ (Over.pullback (Spec.map f.appTop)).obj P) :
    ((Over.pullback T.toSpecΓ).obj Q).left ⟶
      ((Over.pullback f).obj ((Over.pullback S.toSpecΓ).obj P)).left :=
  ((Over.pullback T.toSpecΓ).map a.hom).left ≫
    ((Over.pullbackComp T.toSpecΓ (Spec.map f.appTop)).symm.app P).hom.left ≫
    (eqToIso (congrArg (fun h : T ⟶ Spec Γ(S, ⊤) => (Over.pullback h).obj P)
      (Scheme.toSpecΓ_naturality f).symm)).hom.left ≫
    ((Over.pullbackComp f S.toSpecΓ).app P).hom.left

private def factoredBaseChangeHom {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (ProjectivePresentations.projectiveSpaceOver T n).left ⟶
      ((Over.pullback f).obj (ProjectivePresentations.projectiveSpaceOver S n)).left := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := f.appTop.hom.toAlgebra
  exact pullbackBaseChangeHom f (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n)
    (ProjectivePresentations.affineProjectiveSpace Γ(T, ⊤) n)
    (SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := Γ(S, ⊤)) (A := Γ(T, ⊤)) n)

private theorem mapped_trans4_hom_left {S T : Scheme.{u}}
    {A B : Over S} {C D E : Over T}
    (F : Over S ⥤ Over T) (a : A ≅ B) (b : F.obj B ≅ C) (c : C ≅ D) (d : D ≅ E) :
    ((F.mapIso a) ≪≫ b ≪≫ c ≪≫ d).hom.left =
      (F.map a.hom).left ≫ b.hom.left ≫ c.hom.left ≫ d.hom.left := rfl

private theorem baseChange_hom_factorization {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).hom.left = factoredBaseChangeHom f n := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := f.appTop.hom.toAlgebra
  let P := ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n
  exact mapped_trans4_hom_left (Over.pullback T.toSpecΓ)
    (SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := Γ(S, ⊤)) (A := Γ(T, ⊤)) n)
    ((Over.pullbackComp T.toSpecΓ (Spec.map f.appTop)).symm.app P)
    (eqToIso (congrArg (fun h : T ⟶ Spec Γ(S, ⊤) => (Over.pullback h).obj P)
      (Scheme.toSpecΓ_naturality f).symm))
    ((Over.pullbackComp f S.toSpecΓ).app P)

private theorem pullbackBaseChangeHom_coefficients
    {S T : Scheme.{u}} (f : T ⟶ S)
    (P : Over (Spec Γ(S, ⊤))) (Q : Over (Spec Γ(T, ⊤)))
    (a : Q ≅ (Over.pullback (Spec.map f.appTop)).obj P) :
    pullbackBaseChangeHom f P Q a ≫
      pullback.fst (pullback.snd P.hom S.toSpecΓ) f ≫ pullback.fst P.hom S.toSpecΓ =
    pullback.fst Q.hom T.toSpecΓ ≫ a.hom.left ≫ pullback.fst P.hom (Spec.map f.appTop) := by
  let b := (Over.pullbackComp T.toSpecΓ (Spec.map f.appTop)).symm.app P
  let c := eqToIso (congrArg (fun h : T ⟶ Spec Γ(S, ⊤) => (Over.pullback h).obj P)
    (Scheme.toSpecΓ_naturality f).symm)
  let d := (Over.pullbackComp f S.toSpecΓ).app P
  have hd : d.hom.left ≫ pullback.fst (pullback.snd P.hom S.toSpecΓ) f ≫
      pullback.fst P.hom S.toSpecΓ = pullback.fst P.hom (f ≫ S.toSpecΓ) :=
    Pullback.Comparisons.pullbackComp_hom_fst_fst P S.toSpecΓ f
  have hc : c.hom.left ≫ pullback.fst P.hom (f ≫ S.toSpecΓ) =
      pullback.fst P.hom (T.toSpecΓ ≫ Spec.map f.appTop) :=
    EqualBasePullbackProjections.equalBasePullback_hom_fst P _ _ (Scheme.toSpecΓ_naturality f).symm
  have hb : b.hom.left ≫ pullback.fst P.hom (T.toSpecΓ ≫ Spec.map f.appTop) =
      pullback.fst (pullback.snd P.hom (Spec.map f.appTop)) T.toSpecΓ ≫
        pullback.fst P.hom (Spec.map f.appTop) :=
    pullbackComp_inv_fst P (Spec.map f.appTop) T.toSpecΓ
  let m := ((Over.pullback T.toSpecΓ).map a.hom).left
  exact projection_chain m b.hom.left c.hom.left d.hom.left
    (pullback.fst (pullback.snd P.hom S.toSpecΓ) f) (pullback.fst P.hom S.toSpecΓ)
    (pullback.fst P.hom (f ≫ S.toSpecΓ))
    (pullback.fst P.hom (T.toSpecΓ ≫ Spec.map f.appTop))
    (pullback.fst (pullback.snd P.hom (Spec.map f.appTop)) T.toSpecΓ)
    (pullback.fst P.hom (Spec.map f.appTop))
    (pullback.fst Q.hom T.toSpecΓ) a.hom.left
    (a.hom.left ≫ pullback.fst P.hom (Spec.map f.appTop))
    hd hc hb (Pullback.Comparisons.overPullback_map_left_fst a.hom T.toSpecΓ) rfl

private theorem factoredBaseChangeHom_coefficients
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    factoredBaseChangeHom f n ≫ pullback.fst (ProjectivePresentations.projectiveSpaceOver S n).hom f ≫
        RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection T n ≫ CoefficientFunctoriality.polynomialProjectiveMap f.appTop n := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := f.appTop.hom.toAlgebra
  exact (pullbackBaseChangeHom_coefficients f (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n)
    (ProjectivePresentations.affineProjectiveSpace Γ(T, ⊤) n)
    (SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := Γ(S, ⊤)) (A := Γ(T, ⊤)) n)).trans
      (congrArg (fun k => pullback.fst (ProjectivePresentations.affineProjectiveSpace Γ(T, ⊤) n).hom T.toSpecΓ ≫ k)
        (SpaceBaseChange.affineProjectiveSpaceBaseChangeIso_hom_fst (R := Γ(S, ⊤)) (A := Γ(T, ⊤)) n))

theorem projectiveSpaceOverBaseChangeIso_hom_coefficients
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).hom.left ≫
      pullback.fst (ProjectivePresentations.projectiveSpaceOver S n).hom f ≫ RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
    RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection T n ≫ CoefficientFunctoriality.polynomialProjectiveMap f.appTop n := by
  exact (congrArg (fun k => k ≫ pullback.fst (ProjectivePresentations.projectiveSpaceOver S n).hom f ≫
    RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n) (baseChange_hom_factorization f n)).trans
      (factoredBaseChangeHom_coefficients f n)

theorem projectiveSpaceOverBaseChangeIso_hom_fst
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).hom.left ≫
      pullback.fst (ProjectivePresentations.projectiveSpaceOver S n).hom f = RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n := by
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · exact (Category.assoc _ _ _).trans
      ((projectiveSpaceOverBaseChangeIso_hom_coefficients f n).trans
        (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_fst f n).symm)
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (fun k => k ≫ f) (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).hom.w).trans
      (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_over f n).symm

theorem projectiveSpaceOverBaseChangeIso_inv_baseMap
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n =
      pullback.fst (ProjectivePresentations.projectiveSpaceOver S n).hom f :=
  (((Over.forget T).mapIso (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n)).inv_comp_eq).mpr
    (projectiveSpaceOverBaseChangeIso_hom_fst f n).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangeIsoProjections
