import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldAutomorphismDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualDetection
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LevelBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Automorphism Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent

noncomputable section

section

/-! Full pure polarized automorphisms descend across extensions of an
algebraically closed ground field. Canonical duality reflects the
polarization equation, and faithful pullback reflects the ordered level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

variable {k B : Type} [Field k] [IsAlgClosed k] [Field B]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

def pureAutomorphismOfPullback (b : Spec (.of B) ⟶ Spec (.of k))
    [(Over.pullback b).Faithful]
    (d : A.abelian.scheme ≅ A.abelian.scheme) [IsMonHom d.hom]
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (A.pullback b))
    (hd : (Over.pullback b).map d.hom = e.abelian.hom) : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A := by
  have hdual : (Over.pullback b).map (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap d.hom A.dual A.dual) = e.dual.inv := by
    let e₁ : (A.abelian.pullback b).scheme ≅ (A.abelian.pullback b).scheme := e.abelian
    let : IsMonHom e₁.hom := e.abelianGroup
    have hx := CanonicalDualDetection.inverseDual_eq_canonical e.abelian.hom (A.dual.pullback b)
      (A.dual.pullback b) e.dual e.poincare
    have hb := CanonicalDualBaseChange.canonicalDual_baseChange b d.hom A.dual A.dual
    have hd' : AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap b d.hom = e₁.hom := hd
    exact hb.trans ((CanonicalDualDetection.canonicalDual_congr (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap b d.hom)
      (A.dual.pullback b) (A.dual.pullback b) e₁.hom hd').trans hx.symm)
  have hp : d.hom ≫ A.polarization.isogeny.hom ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap d.hom A.dual A.dual =
      A.polarization.isogeny.hom := by
    apply (Over.pullback b).map_injective
    simp only [Functor.map_comp]
    rw [hdual, hd]
    change e.abelian.hom ≫ (A.pullback b).polarization.isogeny.hom ≫ e.dual.inv = _
    rw [← Category.assoc, ← e.polarization, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  let D := Dual.UnderlyingIso.dualFamilyIso A.dual A.dual d
  have hD : D.inv = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap d.hom A.dual A.dual := CanonicalDualDetection.dualFamilyIso_inv_canonical A.dual A.dual d
  refine {
    abelian := d
    dual := D
    abelianGroup := inferInstance
    dualGroup := inferInstanceAs (IsMonHom (Dual.UnderlyingIso.dualFamilyIso A.dual A.dual d).hom)
    polarization := ?_
    poincare := Dual.PoincareIso.dualFamilyIso_poincare A.dual A.dual d
    level := ?_ }
  · have hh : d.hom ≫ A.polarization.isogeny.hom ≫ D.inv = A.polarization.isogeny.hom := by
      rw [hD]
      exact hp
    have hh' := congrArg (fun z => z ≫ D.hom) hh
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh'.symm
  · apply AbelianScheme.TateComparison.LevelBaseChange.preservesFullLevel_of_pullback A.abelian A.level d.hom b
    rw [hd]
    exact e.level

theorem pure_field_automorphism_descends (b : Spec (.of B) ⟶ Spec (.of k))
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (A.pullback b)) :
    ∃ d : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A, (Over.pullback b).map d.abelian.hom = e.abelian.hom := by
  obtain ⟨r, rfl⟩ := Spec.map_surjective b
  let : Algebra k B := r.hom.toAlgebra
  let e₀ : (A.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).scheme ≅
      (A.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).scheme := e.abelian
  let : IsMonHom e₀.hom := e.abelianGroup
  obtain ⟨d, hd, he⟩ := FieldAutomorphismDescent.FieldDescent.field_group_automorphism_descends k B A.abelian e₀
  let : IsMonHom d.hom := hd
  let : (Over.pullback (Spec.map r)).Faithful := FieldAutomorphismDescent.FieldDescent.fieldBaseChange_faithful k B
  exact ⟨pureAutomorphismOfPullback A (Spec.map r) d e he, he⟩

end

/-! Rigidity transfers through pure polarized isomorphisms and between
extensions of an algebraically closed field of definition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

theorem pure_abelian_eq_id_via {S : Scheme.{0}} {g L : ℕ} {δ : Fin g → ℕ}
    {A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L S}
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) (a : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)
    (h : ∀ j : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B B, j.abelian.hom = 𝟙 B.abelian.scheme) :
    e.abelian.hom = 𝟙 A.abelian.scheme := by
  have hj := h (a.symm.trans (e.trans a))
  change a.abelian.inv ≫ (e.abelian.hom ≫ a.abelian.hom) = 𝟙 B.abelian.scheme at hj
  have hh := congrArg (fun z => a.abelian.hom ≫ z ≫ a.abelian.inv) hj
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.id_comp, Category.comp_id] using hh

theorem pure_fieldPullback_faithful {k B : Type} [Field k] [Field B]
    (b : Spec (.of B) ⟶ Spec (.of k)) : (Over.pullback b).Faithful := by
  have : Surjective b := ⟨Function.surjective_to_subsingleton _⟩
  infer_instance

theorem pure_abelian_eq_id_of_rigid_extension {k B C : Type}
    [Field k] [IsAlgClosed k] [Field B] [Field C]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (b : Spec (.of B) ⟶ Spec (.of k)) (c : Spec (.of C) ⟶ Spec (.of k))
    (hr : ∀ j : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback c) (A.pullback c),
      j.abelian.hom = 𝟙 (A.pullback c).abelian.scheme)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (A.pullback b)) :
    e.abelian.hom = 𝟙 (A.pullback b).abelian.scheme := by
  obtain ⟨d, hd⟩ := pure_field_automorphism_descends A b e
  let : (Over.pullback c).Faithful := pure_fieldPullback_faithful c
  have hc : (Over.pullback c).map d.abelian.hom = 𝟙 (A.pullback c).abelian.scheme :=
    hr (d.pullback c)
  have hi : d.abelian.hom = 𝟙 A.abelian.scheme :=
    (Over.pullback c).map_injective (hc.trans ((Over.pullback c).map_id A.abelian.scheme).symm)
  exact hd.symm.trans ((congrArg (Over.pullback b).map hi).trans
    ((Over.pullback b).map_id A.abelian.scheme))

theorem pure_abelian_eq_id_of_common_model {L k C : Type}
    [Field L] [IsAlgClosed L] [Field k] [Field C]
    {g N : ℕ} {δ : Fin g → ℕ}
    (bk : Spec (.of k) ⟶ Spec (.of L)) (bc : Spec (.of C) ⟶ Spec (.of L))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of L)))
    (Ak : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (Ac : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of C)))
    (ak : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso Ak (A.pullback bk)) (ac : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso Ac (A.pullback bc))
    (hr : ∀ j : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso Ac Ac, j.abelian.hom = 𝟙 Ac.abelian.scheme)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso Ak Ak) : e.abelian.hom = 𝟙 Ak.abelian.scheme := by
  apply pure_abelian_eq_id_via e ak
  intro j
  apply pure_abelian_eq_id_of_rigid_extension A bk bc _ j
  intro l
  exact pure_abelian_eq_id_via l ac.symm hr

def purePullbackFactor {S T U : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S) (w : f ≫ h = x) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback x) ((A.pullback h).pullback f) := by
  subst x
  exact (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A h f).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent
