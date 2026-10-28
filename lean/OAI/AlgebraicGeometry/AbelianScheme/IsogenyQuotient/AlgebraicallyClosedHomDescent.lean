import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldEndomorphismDescent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianProducts

/-! # Algebraically Closed Hom Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedHomDescent.Construction

noncomputable section

/-! Homomorphisms between two abelian varieties descend through any
extension of an algebraically closed field. Apply endomorphism descent
to their product and recover the off-diagonal component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosed_field_hom_descends
    (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (f : (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).scheme ⟶
      (B.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).scheme) [IsMonHom f] :
    ∃ w : A.scheme ⟶ B.scheme, IsMonHom w ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map w = f := by
  let u := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := Over.pullback u
  let P := PELModuli.CMPoints.AbelianProducts.abelianProduct A B
  let productGroup : GrpObj (A.scheme ⊗ B.scheme) := P.group
  let Ak := F.obj A.scheme
  let Bk := F.obj B.scheme
  let groupAk : GrpObj Ak := (A.pullback u).group
  let groupBk : GrpObj Bk := (B.pullback u).group
  let groupPk : GrpObj (F.obj (A.scheme ⊗ B.scheme)) := (P.pullback u).group
  let f' : Ak ⟶ Bk := f
  have : IsMonHom f' := ‹IsMonHom f›
  let c : Ak ⊗ Bk ≅ F.obj (A.scheme ⊗ B.scheme) := Functor.Monoidal.μIso F A.scheme B.scheme
  have hc : c.inv = lift (F.map (fst A.scheme B.scheme)) (F.map (snd A.scheme B.scheme)) :=
    Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory F A.scheme B.scheme
  have : IsMonHom c.inv := by rw [hc]; infer_instance
  have : IsMonHom c.symm.hom := ‹IsMonHom c.inv›
  have : IsMonHom c.hom := inferInstanceAs (IsMonHom c.symm.inv)
  let a : (P.pullback u).scheme ⟶ (P.pullback u).scheme :=
    c.inv ≫ lift (1 : Ak ⊗ Bk ⟶ Ak) (fst Ak Bk ≫ f') ≫ c.hom
  have : IsMonHom (1 : Ak ⊗ Bk ⟶ Ak) := by rw [Hom.one_def]; infer_instance
  have ht : IsMonHom (lift (1 : Ak ⊗ Bk ⟶ Ak) (fst Ak Bk ≫ f')) := inferInstance
  have htc : IsMonHom (lift (1 : Ak ⊗ Bk ⟶ Ak) (fst Ak Bk ≫ f') ≫ c.hom) :=
    @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ ht ‹IsMonHom c.hom›
  have : IsMonHom a :=
    @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ ‹IsMonHom c.inv› htc
  obtain ⟨v, hv, hbase⟩ := AbelianModuli.ReferenceFamily.FieldEndomorphismDescent.FieldDescent.field_endomorphism_descends k K P a
  have : IsMonHom v := hv
  let v' : A.scheme ⊗ B.scheme ⟶ A.scheme ⊗ B.scheme := v
  have : IsMonHom v' := hv
  have hv' : F.map v' = a := hbase
  let w : A.scheme ⟶ B.scheme := lift (𝟙 A.scheme) (1 : A.scheme ⟶ B.scheme) ≫ v' ≫ snd A.scheme B.scheme
  have : IsMonHom (1 : A.scheme ⟶ B.scheme) := by rw [Hom.one_def]; infer_instance
  have hincl : IsMonHom (lift (𝟙 A.scheme) (1 : A.scheme ⟶ B.scheme)) := inferInstance
  have hvs : IsMonHom (v' ≫ snd A.scheme B.scheme) :=
    @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ ‹IsMonHom v'›
      (inferInstanceAs (IsMonHom (snd A.scheme B.scheme)))
  have hw : IsMonHom w :=
    @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hincl hvs
  refine ⟨w, hw, ?_⟩
  have hi : F.map (lift (𝟙 A.scheme) (1 : A.scheme ⟶ B.scheme)) ≫ c.inv =
      lift (𝟙 Ak) (1 : Ak ⟶ Bk) := by
    exact (Functor.OplaxMonoidal.lift_δ F (𝟙 A.scheme) (1 : A.scheme ⟶ B.scheme)).trans
      (congrArg₂ lift (F.map_id A.scheme) (F.map_one (X := A.scheme) (M := B.scheme)))
  have hs : c.hom ≫ F.map (snd A.scheme B.scheme) = snd Ak Bk :=
    Functor.Monoidal.μ_snd F A.scheme B.scheme
  change F.map w = f'
  simp only [w, Functor.map_comp, hv']
  change F.map (lift (𝟙 A.scheme) (1 : A.scheme ⟶ B.scheme)) ≫
    (c.inv ≫ lift (1 : Ak ⊗ Bk ⟶ Ak) (fst Ak Bk ≫ f') ≫ c.hom) ≫
      F.map (snd A.scheme B.scheme) = f'
  simp only [Category.assoc, hs]
  rw [← Category.assoc, hi, lift_snd, ← Category.assoc, lift_fst, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedHomDescent.Construction
