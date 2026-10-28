import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo

/-! # Scalar Forms Change -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange.FormsScalarChange

/-! Differential forms and their differential are unchanged under an equivalent base field. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

variable {R S A : Type} [Field R] [Field S] [CommRing A] [Algebra R A] [Algebra S A]
  (σ : R ≃+* S) (hσ : algebraMap R A = (algebraMap S A).comp σ.toRingHom)

def changeRelation {n : ℕ} : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n → AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex S A n
  | .add v i x y => .add v i x y
  | .mul v i x y => .mul v i x y
  | .base v i r => .base v i (σ r)
  | .alt v i j hij hne => .alt v i j hij hne

include hσ in
theorem relation_change {n : ℕ} (r : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation R A n r = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation S A n (changeRelation σ r) := by
  cases r with
  | base v i r =>
      change Finsupp.single (Function.update v i (algebraMap R A r)) 1 =
        Finsupp.single (Function.update v i (algebraMap S A (σ r))) 1
      rw [DFunLike.congr_fun hσ r]
      rfl
  | add => rfl
  | mul => rfl
  | alt => rfl

include hσ in
theorem relations_le (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n ≤ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  rw [relation_change σ hσ r]
  exact Submodule.subset_span (Set.mem_range_self _)

include hσ in
theorem inverse_scalars : algebraMap S A = (algebraMap R A).comp σ.symm.toRingHom := by
  apply RingHom.ext
  intro s
  have h := DFunLike.congr_fun hσ (σ.symm s)
  change algebraMap R A (σ.symm s) = algebraMap S A (σ (σ.symm s)) at h
  rw [σ.apply_symm_apply] at h
  exact h.symm

include hσ in
theorem relations_eq (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n :=
  le_antisymm (relations_le σ hσ n) (relations_le σ.symm (inverse_scalars σ hσ) n)

def formEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A n :=
  Submodule.quotEquivOfEq _ _ (relations_eq σ hσ n)

theorem formEquiv_symbol {n : ℕ} (a : A) (v : Fin n → A) :
    formEquiv σ hσ n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S A a v :=
  Submodule.quotEquivOfEq_mk _ _ (relations_eq σ hσ n) (Finsupp.single v a)

theorem formEquiv_differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formEquiv σ hσ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n (formEquiv σ hσ n ω) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v a =>
      change formEquiv σ hσ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n (formEquiv σ hσ n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol, formEquiv_symbol]

def semilinearEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₛₗ[σ.toRingHom] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A n where
  __ := (formEquiv σ hσ n).toAddEquiv
  map_smul' r ω := by
    change formEquiv σ hσ n (r • ω) = σ r • formEquiv σ hσ n ω
    rw [← IsScalarTower.algebraMap_smul A r ω, (formEquiv σ hσ n).map_smul]
    have hr : algebraMap R A r = algebraMap S A (σ r) := DFunLike.congr_fun hσ r
    rw [hr, IsScalarTower.algebraMap_smul]

theorem semilinearEquiv_symbol {n : ℕ} (a : A) (v : Fin n → A) :
    semilinearEquiv σ hσ n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S A a v :=
  formEquiv_symbol σ hσ a v

theorem semilinearEquiv_differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    semilinearEquiv σ hσ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n (semilinearEquiv σ hσ n ω) :=
  formEquiv_differential σ hσ n ω

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal in
theorem formEquiv_naturality {B : Type} [CommRing B] [Algebra R B] [Algebra S B]
    (hB : algebraMap R B = (algebraMap S B).comp σ.toRingHom)
    (fR : CommAlgCat.of R A ⟶ CommAlgCat.of R B)
    (fS : CommAlgCat.of S A ⟶ CommAlgCat.of S B) (hf : ∀ a, fR a = fS a)
    (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formEquiv σ hB n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap fR n ω) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap fS n (formEquiv σ hσ n ω) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v a =>
      change formEquiv σ hB n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap fR n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap fS n (formEquiv σ hσ n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
      erw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, formEquiv_symbol, formEquiv_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
      congr 1
      · exact hf a
      · funext i
        exact hf (v i)

end NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange.FormsScalarChange

namespace NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange.SectionScalarChange
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
section

/-! The actual section-ring scalar maps under a change of the scheme's base ring. -/

variable {R S : Type} [CommRing R] [CommRing S]
  (ρ : R →+* S) (X : Over (Spec (CommRingCat.of S)))

def restrictBase : Over (Spec (CommRingCat.of R)) :=
  (Over.map (Spec.map (CommRingCat.ofHom ρ))).obj X

theorem sectionBase_comp (U : X.left.Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (restrictBase ρ X).hom.appLE ⊤ U le_top =
      CommRingCat.ofHom ρ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
        X.hom.appLE ⊤ U le_top := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (X.hom ≫ Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ U _ = _
  rw [← Scheme.Hom.appLE_comp_appLE X.hom (Spec.map (CommRingCat.ofHom ρ))
    ⊤ ⊤ U le_top le_top]
  have htop : (Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom ρ)).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  rw [htop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem sectionBaseMap_comp (U : X.left.Opens) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R (restrictBase ρ X) U =
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap S X U).comp ρ :=
  congrArg (fun f : CommRingCat.of R ⟶ Γ(X.left, U) => f.hom) (sectionBase_comp ρ X U)

end

/-! The canonical generic-fiber isomorphism when the coefficient field is replaced by an equivalent ring. -/

variable {B R S : Type} [CommRing B] [CommRing R] [CommRing S]
  (σ : R ≃+* S) (r : B →+* R) (s : B →+* S) (hs : s = σ.toRingHom.comp r)

include hs in
theorem baseMap_comp : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom r) = Spec.map (CommRingCat.ofHom s) := by
  rw [← Spec.map_comp]
  exact congrArg (fun t : B →+* S => Spec.map (CommRingCat.ofHom t)) hs.symm

def pullbackAlongEquivIso :
    Over.pullback (Spec.map (CommRingCat.ofHom s)) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom r)) ⋙
        Over.pullback (Spec.map (CommRingCat.ofHom σ.toRingHom)) :=
  eqToIso (congrArg (fun f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B) => Over.pullback f)
    (baseMap_comp σ r s hs).symm) ≪≫ Over.pullbackComp _ _

def restrictPullbackIso :
    Over.pullback (Spec.map (CommRingCat.ofHom s)) ⋙
        Over.map (Spec.map (CommRingCat.ofHom σ.toRingHom)) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom r)) := by
  let f := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let g := Spec.map (CommRingCat.ofHom r)
  letI : IsIso f := (Scheme.Spec.mapIso σ.toCommRingCatIso.op).isIso_hom
  let c : Over.pullback f ⋙ Over.map f ≅ 𝟭 _ := asIso (Over.mapPullbackAdj f).counit
  exact Functor.isoWhiskerRight (pullbackAlongEquivIso σ r s hs) (Over.map f) ≪≫
    Functor.associator (Over.pullback g) (Over.pullback f) (Over.map f) ≪≫
    Functor.isoWhiskerLeft (Over.pullback g) c ≪≫ Functor.rightUnitor _

def restrictedFiberIso (X : Over (Spec (CommRingCat.of B))) :
    restrictBase σ.toRingHom ((Over.pullback (Spec.map (CommRingCat.ofHom s))).obj X) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom r))).obj X :=
  (restrictPullbackIso σ r s hs).app X

end NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange.SectionScalarChange

end

end OAI
