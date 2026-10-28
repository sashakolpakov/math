import OAI.ArithmeticGeometry.Models.SpreadingOut.Finite

/-! # Diagram -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram.Construction

noncomputable section

/-! Simultaneous arithmetic models with compatible specified morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v w

theorem coefficient_arithmetic_base
    {K : Type u} [Field K] [NumberField K] (s : Finset K) :
    ∃ (B : Base.Construction.ArithmeticOpen K) (b : B.U.toScheme ⟶ CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s),
      B.generic ≫ b = CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s := by
  let A := CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s
  obtain ⟨d, hd, hpow, hle⟩ := Fg.Construction.fg_subalgebra_le_localization A ⟨s, rfl⟩
  let R₀ := Localization.subalgebra.ofField K (Submonoid.powers d) hpow
  let φ : A →ₐ[𝓞 K] R₀ := Subalgebra.inclusion hle
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R₀ K))
  have hgf : g ≫ f = CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s := by
    rw [← Spec.map_comp]
    rfl
  let B := Base.Construction.arithmeticOpenOfNonzero K d hd
  let j : Spec (.of R₀) ≅ B.U.toScheme := Affine.Construction.localizationOpenIso (𝓞 K) R₀ d
  have hj : j.hom ≫ B.U.ι = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) R₀)) :=
    Affine.Construction.localizationOpenIso_hom_ι (𝓞 K) R₀ d
  have hg : g ≫ j.hom = B.generic := by
    apply (cancel_mono B.U.ι).mp
    rw [Category.assoc, hj, B.generic_eq]
    change Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) R₀)) = _
    rw [← Spec.map_comp]
    congr 1
  refine ⟨B, j.inv ≫ f, ?_⟩
  rw [← hg, Category.assoc, Iso.hom_inv_id_assoc, hgf]

theorem cartesian_generic_iso_compatibility
    {S T : Scheme.{u}} (g : T ⟶ S) {X Y : Over T} {M N : Over S}
    (p : X.left ⟶ M.left) (q : Y.left ⟶ N.left)
    (hp : IsPullback p X.hom M.hom g) (hq : IsPullback q Y.hom N.hom g)
    (f : X ⟶ Y) (a : M ⟶ N) (ha : p ≫ a.left = f.left ≫ q) :
    (Over.pullback g).map a ≫ (Over.isoMk hq.isoPullback.symm hq.isoPullback_inv_snd).hom =
      (Over.isoMk hp.isoPullback.symm hp.isoPullback_inv_snd).hom ≫ f := by
  let eX : (Over.pullback g).obj M ≅ X :=
    Over.isoMk hp.isoPullback.symm hp.isoPullback_inv_snd
  let eY : (Over.pullback g).obj N ≅ Y :=
    Over.isoMk hq.isoPullback.symm hq.isoPullback_inv_snd
  change (Over.pullback g).map a ≫ eY.hom = eX.hom ≫ f
  apply (cancel_epi eX.inv).mp
  apply (cancel_mono eY.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (hp.isoPullback.hom ≫ ((Over.pullback g).map a).left) ≫ pullback.fst N.hom g =
      (f.left ≫ hq.isoPullback.hom) ≫ pullback.fst N.hom g
    erw [Category.assoc, pullback.lift_fst, ← Category.assoc, hp.isoPullback_hom_fst,
      Category.assoc, hq.isoPullback_hom_fst]
    exact ha
  · change (hp.isoPullback.hom ≫ ((Over.pullback g).map a).left) ≫ pullback.snd N.hom g =
      (f.left ≫ hq.isoPullback.hom) ≫ pullback.snd N.hom g
    erw [Category.assoc, pullback.lift_snd, hp.isoPullback_hom_snd,
      Category.assoc, hq.isoPullback_hom_snd]
    exact f.w.symm

theorem finite_smooth_proper_diagram_arithmetic_model
    {K : Type u} [Field K] [NumberField K] {ι : Type v} {α : Type w}
    [Finite ι] [Finite α]
    (X : ι → Over (Base.Construction.fieldBase K)) (hs : ∀ i, Smooth (X i).hom)
    (hp : ∀ i, IsProper (X i).hom) (src dst : α → ι)
    (f : ∀ a, X (src a) ⟶ X (dst a)) :
    ∃ (B : Base.Construction.ArithmeticOpen K) (M : ι → Over B.U.toScheme)
      (fM : ∀ a, M (src a) ⟶ M (dst a))
      (e : ∀ i, (Over.pullback B.generic).obj (M i) ≅ X i),
      (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom) ∧
      (∀ a, (Over.pullback B.generic).map (fM a) ≫ (e (dst a)).hom =
        (e (src a)).hom ≫ f a) := by
  obtain ⟨s, M, p, fM, hM, hcart, hfM⟩ :=
    SpreadingOut.Finite.Construction.finite_smooth_proper_arrows_coefficient_model X hs hp src dst f
  let g := CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s
  let e (i : ι) : (Over.pullback g).obj (M i) ≅ X i :=
    Over.isoMk (hcart i).isoPullback.symm (hcart i).isoPullback_inv_snd
  have he (a : α) : (Over.pullback g).map (fM a) ≫ (e (dst a)).hom =
      (e (src a)).hom ≫ f a :=
    cartesian_generic_iso_compatibility g _ _ (hcart _) (hcart _) (f a) (fM a) (hfM a)
  obtain ⟨B, b, hb⟩ := coefficient_arithmetic_base s
  let F := Over.pullback b
  let G := Over.pullback B.generic
  let c : F ⋙ G ≅ Over.pullback g :=
    (Over.pullbackComp B.generic b).symm ≪≫
      eqToIso (congrArg (fun k : Base.Construction.fieldBase K ⟶ CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s ↦ Over.pullback k) hb)
  refine ⟨B, (fun i ↦ F.obj (M i)), (fun a ↦ F.map (fM a)),
    (fun i ↦ c.app (M i) ≪≫ e i), ?_, ?_⟩
  · intro i
    have := (hM i).1
    have := (hM i).2
    exact ⟨inferInstanceAs (Smooth (pullback.snd (M i).hom b)),
      inferInstanceAs (IsProper (pullback.snd (M i).hom b))⟩
  · intro a
    have hc : G.map (F.map (fM a)) ≫ (c.app (M (dst a))).hom =
        (c.app (M (src a))).hom ≫ (Over.pullback g).map (fM a) :=
      c.hom.naturality (fM a)
    change G.map (F.map (fM a)) ≫ (c.app (M (dst a))).hom ≫ (e (dst a)).hom =
      ((c.app (M (src a))).hom ≫ (e (src a)).hom) ≫ f a
    rw [← Category.assoc, hc, Category.assoc, he,
      Category.assoc]

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram.Construction
