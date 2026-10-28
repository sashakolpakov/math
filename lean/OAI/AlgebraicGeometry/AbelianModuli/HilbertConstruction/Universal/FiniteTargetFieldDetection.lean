import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FiniteTargetFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterLevelPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackMapEquality

/-! # Finite Target Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.FiniteTargetFieldDetection

noncomputable section

/-! Finite-target pointed-map detection holds on every test scheme of
fixed Noetherian projective abelian families. Local-ring pullbacks remove
the affine restriction without requiring descent of the finite target. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsNoetherian S] {g h : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
variable (T : Over S) (D : Over T.left) [GrpObj D]
variable (r : D ⟶ (B.pullback T.hom).scheme) [IsMonHom r] [IsFinite r.left]

include PA PB r in
theorem universalFiniteTarget_pointedMap_eq_of_fieldPullbacks
    (f q : (A.pullback T.hom).scheme ⟶ D)
    (hf : η[(A.pullback T.hom).scheme] ≫ f = η[D])
    (hq : η[(A.pullback T.hom).scheme] ≫ q = η[D])
    (he : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  apply HilbertConstruction.Over.HomLocalRingDetection.overHom_eq_of_allLocalRingPullbacks
  intro R _ _ s
  let U : Over S := Over.mk (s ≫ T.hom)
  let c : U ⟶ T := Over.homMk s rfl
  let F : Over T.left ⥤ Over U.left := Over.pullback s
  let eA : (A.pullback U.hom).scheme ≅ F.obj (A.pullback T.hom).scheme := A.parameterPullbackIso c
  let eB : (B.pullback U.hom).scheme ≅ F.obj (B.pullback T.hom).scheme := B.parameterPullbackIso c
  let : IsMonHom eA.hom := Abelian.Schemes.AbelianScheme.parameterPullbackIso_isMonHom c A
  let : IsIso eB.inv.left :=
    inferInstanceAs (IsIso (((Over.forget U.left).mapIso eB).inv))
  let : IsMonHom eB.inv :=
    Abelian.Schemes.AbelianScheme.parameterPullbackIso_symm_isMonHom c B
  let : IsFinite eB.inv.left := inferInstance
  let : IsAffine U.left := inferInstanceAs (IsAffine (Spec (.of R)))
  let r' : F.obj D ⟶ (B.pullback U.hom).scheme := F.map r ≫ eB.inv
  let : IsFinite (F.map r).left :=
    MorphismProperty.of_isPullback (Projective.PresentationBaseChange.overPullback_map_isPullback r s) inferInstance
  let : IsFinite r'.left := inferInstanceAs (IsFinite ((F.map r).left ≫ eB.inv.left))
  let : IsMonHom r' := inferInstanceAs (IsMonHom (F.map r ≫ eB.inv))
  have hF : η[((A.pullback T.hom).pullback s).scheme] ≫ F.map f = η[F.obj D] :=
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff F f).mpr (congrArg F.map hf)
  have hQ : η[((A.pullback T.hom).pullback s).scheme] ≫ F.map q = η[F.obj D] :=
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff F q).mpr (congrArg F.map hq)
  apply (cancel_epi eA.hom).mp
  refine Relative.FiniteTargetFieldDetection.relativeFiniteTarget_pointedMap_eq_of_fieldPullbacks A B PA PB U (F.obj D) r'
    (eA.hom ≫ F.map f) (eA.hom ≫ F.map q) ?_ ?_ ?_
  · rw [← Category.assoc, IsMonHom.one_hom, hF]
  · rw [← Category.assoc, IsMonHom.one_hom, hQ]
  · intro K _ t
    have h : (Over.pullback t).map (F.map f) = (Over.pullback t).map (F.map q) :=
      (Iterated.PullbackMapEquality.overPullback_map_eq_iff_iterated t s f q).mp (he K (t ≫ s))
    rw [Functor.map_comp, Functor.map_comp, h]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.FiniteTargetFieldDetection
