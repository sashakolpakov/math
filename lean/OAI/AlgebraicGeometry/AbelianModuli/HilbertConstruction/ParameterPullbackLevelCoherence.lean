import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterLevelPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TransportComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Parameter Pullback Level Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The native parameter-pullback comparison is the usual composition
comparison followed by equality of structural maps. It therefore preserves
the original ordered full level for every parameter morphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S V : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.pullbackCongrIso_hom_fst (b c : V ⟶ S) (h : b = c) :
    (A.pullbackCongrIso b c h).hom.left ≫ pullback.fst A.scheme.hom c = pullback.fst A.scheme.hom b := by
  cases h
  exact Category.id_comp _

variable {U T : Over S} (f : U ⟶ T)

theorem Abelian.Schemes.AbelianScheme.parameterPullbackIso_symm_eq :
    (A.parameterPullbackIso f).symm = (A.pullbackCompIso T.hom f.left).symm ≪≫
      A.pullbackCongrIso (f.left ≫ T.hom) U.hom f.w := by
  let q := (A.pullbackCompIso T.hom f.left).symm ≪≫
    A.pullbackCongrIso (f.left ≫ T.hom) U.hom f.w
  have he : (A.parameterPullbackIso f).inv.left ≫ pullback.fst A.scheme.hom U.hom =
      pullback.fst (A.pullback T.hom).scheme.hom f.left ≫ pullback.fst A.scheme.hom T.hom :=
    ParameterLevelPointComparison.singleParameterBaseChangeIso_inv_original_fst f A.scheme
  have hq : q.hom.left ≫ pullback.fst A.scheme.hom U.hom =
      pullback.fst (A.pullback T.hom).scheme.hom f.left ≫ pullback.fst A.scheme.hom T.hom := by
    change ((A.pullbackCompIso T.hom f.left).inv.left ≫
      (A.pullbackCongrIso (f.left ≫ T.hom) U.hom f.w).hom.left) ≫ pullback.fst A.scheme.hom U.hom = _
    erw [Category.assoc, A.pullbackCongrIso_hom_fst, A.pullbackCompIso_inv_left_fst]
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact he.trans hq.symm
  · exact (A.parameterPullbackIso f).inv.w.trans q.hom.w.symm

theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_parameterPullback (l : A.FullLevel N) :
    ((l.pullback T.hom).pullback f.left).transport (A.parameterPullbackIso f).symm = l.pullback U.hom := by
  have hh : ∀ (e : ((A.pullback T.hom).pullback f.left).scheme ≅ (A.pullback U.hom).scheme)
      [IsMonHom e.hom],
      e = (A.pullbackCompIso T.hom f.left).symm ≪≫
        A.pullbackCongrIso (f.left ≫ T.hom) U.hom f.w →
      ((l.pullback T.hom).pullback f.left).transport e = l.pullback U.hom := by
    intro e _ he
    subst e
    rw [← Abelian.Schemes.AbelianScheme.FullLevel.transport_trans, Abelian.Schemes.AbelianScheme.FullLevel.transport_pullbackComp,
      Abelian.Schemes.AbelianScheme.FullLevel.transport_pullbackCongr]
  exact hh _ (A.parameterPullbackIso_symm_eq f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
