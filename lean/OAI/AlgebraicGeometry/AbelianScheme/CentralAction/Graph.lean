import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Graph -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Graph.Construction

noncomputable section

/-! A finite etale correspondence with one geometric branch at every
source point is an actual graph. The inverse source map is descended. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale

/-- Surjectivity on all algebraically closed points implies scheme
surjectivity, using the algebraic closure of each residue field. -/
theorem surjective_of_geometric_lifts {B : Scheme} {X Y : Over B}
    (f : X ⟶ Y)
    (hlift : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (b : Spec (.of k) ⟶ B) (y : Over.mk b ⟶ Y),
        ∃ x : Over.mk b ⟶ X, x ≫ f = y) : Surjective f.left := by
  constructor
  intro y
  let k := AlgebraicClosure (Y.left.residueField y)
  let p : Spec (.of k) ⟶ Spec (Y.left.residueField y) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) k))
  let a := p ≫ Y.left.fromSpecResidueField y
  let b := a ≫ Y.hom
  let z : Over.mk b ⟶ Y := Over.homMk a rfl
  obtain ⟨x, hx⟩ := hlift k b z
  refine ⟨x.left (default : Spec (.of k)), ?_⟩
  have he := congrArg (fun m => m.left (default : Spec (.of k))) hx
  change f.left (x.left _) = (Y.left.fromSpecResidueField y) (p _) at he
  exact he.trans (Scheme.fromSpecResidueField_apply y _)

/-- Geometric singleton fibers give a source isomorphism on the whole
reduced moduli scheme, including all of its components. -/
theorem finite_etale_isIso_of_geometric_bijective {B : Scheme} {X Y : Over B}
    [IsReduced Y.left] [IsLocallyNoetherian Y.left] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (hbij : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (b : Spec (.of k) ⟶ B),
      Function.Bijective (fun x : Over.mk b ⟶ X => x ≫ f)) : IsIso f := by
  have : Surjective f.left := surjective_of_geometric_lifts f
    (fun k _ _ b y => (hbij k b).2 y)
  have : IsReduced X.left := TateComparison.Etale.etale_source_reduced f.left
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian f.left
  have : IsSeparated X.hom := by
    rw [← f.w]
    infer_instance
  let R : Over B := Over.mk (pullback.fst f.left f.left ≫ X.hom)
  have : IsReduced R.left := TateComparison.Etale.etale_source_reduced (pullback.fst f.left f.left)
  let r₁ : R ⟶ X := Over.homMk (pullback.fst f.left f.left) rfl
  let r₂ : R ⟶ X := Over.homMk (pullback.snd f.left f.left) (by
    change pullback.snd f.left f.left ≫ X.hom = pullback.fst f.left f.left ≫ X.hom
    rw [← f.w, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hr : r₁ ≫ f = r₂ ≫ f := Over.OverMorphism.ext pullback.condition
  have he : r₁ = r₂ := by
    apply TateComparison.GeometricExt.over_hom_ext_geometric
    intro k _ _ b z
    apply (hbij k b).1
    change (z ≫ r₁) ≫ f = (z ≫ r₂) ≫ f
    rw [Category.assoc, Category.assoc, hr]
  have hp : pullback.fst f.left f.left = pullback.snd f.left f.left :=
    congrArg (fun z => z.left) he
  have hc : ∀ {W : Scheme} (a b : W ⟶ X.left), a ≫ f.left = b ≫ f.left → a = b := by
    intro W a b hab
    have hz := congrArg (fun z => pullback.lift a b hab ≫ z) hp
    simpa only [pullback.lift_fst, pullback.lift_snd] using hz
  let g := EffectiveEpi.desc f.left (𝟙 X.left) (by
    intro W a b hab
    simp only [Category.comp_id]
    exact hc a b hab)
  have hfg : f.left ≫ g = 𝟙 X.left := EffectiveEpi.fac _ _ _
  have hgf : g ≫ f.left = 𝟙 Y.left := by
    apply (cancel_epi f.left).mp
    rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
  let e : X.left ≅ Y.left := ⟨f.left, g, hfg, hgf⟩
  have : IsIso ((Over.forget B).map f) := e.isIso_hom
  exact isIso_of_reflects_iso f (Over.forget B)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Graph.Construction
