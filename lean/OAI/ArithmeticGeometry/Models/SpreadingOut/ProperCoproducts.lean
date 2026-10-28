import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.VanKampen

/-! # Proper Coproducts -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction

noncomputable section

/-! Finite disjoint unions of proper models and their base changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem sigma_map_component_pullback {ι : Type u} {X Y : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y i) (i : ι) :
    IsPullback (f i) (Sigma.ι X i) (Sigma.ι Y i) (Limits.Sigma.map f) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hy⟩
    obtain ⟨⟨j, x⟩, rfl⟩ := (sigmaMk X).surjective x
    have he : Sigma.ι Y i y = Sigma.ι Y j (f j x) := by
      simpa only [sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_map] using hy
    obtain rfl : i = j := congrArg Sigma.fst ((sigmaι_eq_iff Y i j _ _).mp he)
    exact ⟨x, by simp⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f i x, by simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]⟩

theorem proper_sigma_map {ι : Type u} {X Y : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, IsProper (f i)) : IsProper (Limits.Sigma.map f) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (sigmaOpenCover Y) ?_
  intro i
  change IsProper (pullback.snd (Limits.Sigma.map f) (Sigma.ι Y i))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    (sigma_map_component_pullback f i).flip.isoPullback.hom]
  convert hf i using 1
  exact (sigma_map_component_pullback f i).flip.isoPullback_hom_snd

theorem finite_affine_fold (R : Type u) [CommRing R] (ι : Type u) [Finite ι] :
    IsFinite (Sigma.desc (fun _ : ι ↦ 𝟙 (Spec (.of R)))) := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap R (ι → R)))
  have : IsFinite q := by
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  have he : Sigma.desc (fun _ : ι ↦ 𝟙 (Spec (.of R))) =
      sigmaSpec (fun _ : ι ↦ CommRingCat.of R) ≫ q := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, ι_sigmaSpec_assoc]
    change 𝟙 _ = Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ι ↦ R) i)) ≫ q
    rw [← Spec.map_comp]
    convert (Spec.map_id (CommRingCat.of R)).symm using 1
    congr 1
  rw [he]
  infer_instance

theorem proper_finite_sigma_desc (R : Type u) [CommRing R]
    {ι : Type u} [Finite ι] {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ Spec (.of R)) (hf : ∀ i, IsProper (f i)) :
    IsProper (Sigma.desc f) := by
  have := proper_sigma_map f hf
  have := finite_affine_fold R ι
  have he : Sigma.desc f = Limits.Sigma.map f ≫
      Sigma.desc (fun _ : ι ↦ 𝟙 (Spec (.of R))) := by
    apply Sigma.hom_ext
    intro i
    simp
  rw [he]
  infer_instance

def overSigma {S : Scheme.{u}} {ι : Type u} (P : ι → Over S) : Over S :=
  Over.mk (Sigma.desc (fun i ↦ (P i).hom))

def overSigmaDesc {S : Scheme.{u}} {ι : Type u} {P : ι → Over S}
    {X : Over S} (f : ∀ i, P i ⟶ X) : overSigma P ⟶ X :=
  Over.homMk (Sigma.desc (fun i ↦ (f i).left)) (by
    change Sigma.desc (fun i ↦ (f i).left) ≫ X.hom = Sigma.desc (fun i ↦ (P i).hom)
    apply Sigma.hom_ext
    intro i
    simp)

def overSigmaIso {S : Scheme.{u}} {ι : Type u} {P Q : ι → Over S}
    (e : ∀ i, P i ≅ Q i) : overSigma P ≅ overSigma Q :=
  Over.isoMk (Limits.Sigma.mapIso (fun i ↦ (Over.forget S).mapIso (e i))) (by
    change (Limits.Sigma.mapIso (fun i ↦ (Over.forget S).mapIso (e i))).hom ≫
      Sigma.desc (fun i ↦ (Q i).hom) = Sigma.desc (fun i ↦ (P i).hom)
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_mapIso_hom, Category.assoc]
    change (e i).hom.left ≫ Sigma.ι (fun i ↦ (Q i).left) i ≫
      Sigma.desc (fun i ↦ (Q i).hom) =
      Sigma.ι (fun i ↦ (P i).left) i ≫ Sigma.desc (fun i ↦ (P i).hom)
    simp)

theorem sigma_cartesian {S T : Scheme.{u}} (g : T ⟶ S)
    {ι : Type u} [Finite ι] (P : ι → Over S) (Q : ι → Over T)
    (p : ∀ i, (Q i).left ⟶ (P i).left)
    (hp : ∀ i, IsPullback (p i) (Q i).hom (P i).hom g) :
    IsPullback (Sigma.desc (fun i ↦ p i ≫ Sigma.ι (fun i ↦ (P i).left) i))
      (overSigma Q).hom (overSigma P).hom g := by
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (fun i ↦ (P i).left))
  have H := hu.isPullback_of_isColimit_right (fun i ↦ (P i).hom)
    (overSigma P).hom g p (fun i ↦ (Q i).hom) hp
    (coproductIsCoproduct (fun i ↦ (Q i).left))
    (by intro i; simp [overSigma])
  have hd {A : Scheme.{u}} (k : ∀ i, (Q i).left ⟶ A) :
      Cofan.IsColimit.desc (coproductIsCoproduct (fun i ↦ (Q i).left)) k = Sigma.desc k := by
    apply Sigma.hom_ext
    intro i
    simp [Cofan.IsColimit.desc, coproductIsCoproduct]
  simpa only [hd, cofan_mk_inj, Cofan.mk_pt, overSigma, Over.mk_hom] using H

def overSigmaBaseChangeIso {S T : Scheme.{u}} (g : T ⟶ S)
    {ι : Type u} [Finite ι] (P : ι → Over S) :
    (Over.pullback g).obj (overSigma P) ≅
      overSigma (fun i ↦ (Over.pullback g).obj (P i)) := by
  let h := sigma_cartesian g P (fun i ↦ (Over.pullback g).obj (P i))
    (fun i ↦ pullback.fst (P i).hom g) (fun i ↦ .of_hasPullback _ _)
  exact Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction
