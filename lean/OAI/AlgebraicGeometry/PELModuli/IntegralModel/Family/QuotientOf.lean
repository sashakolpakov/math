import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverKernelPairFactor

/-! # Quotient Of -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf

noncomputable section

section

/-! A compatible local section descends to a section of the actual
quotient family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem family_quotient_section_descends {B T X W Z : Scheme.{0}}
    (u : T ⟶ B) [EffectiveEpi u] (a : X ⟶ T)
    (Y : Over B) (q : X ⟶ Y.left) (hbase : q ≫ Y.hom = a ≫ u)
    (s t : W ⟶ T) (hu : IsKernelPair u s t)
    (v w : Z ⟶ X) (hq : v ≫ q = w ≫ q)
    (z : T ⟶ X) (hz : z ≫ a = 𝟙 T) (r : W ⟶ Z)
    (hs : r ≫ v = s ≫ z) (ht : r ≫ w = t ≫ z) :
    ∃! d : Over.mk (𝟙 B) ⟶ Y, u ≫ d.left = z ≫ q := by
  let T' : Over B := Over.mk u
  let u' : T' ⟶ Over.mk (𝟙 B) := Over.homMk u (Category.comp_id u)
  have : EffectiveEpi u'.left := inferInstanceAs (EffectiveEpi u)
  let f : T' ⟶ Y := Over.homMk (z ≫ q) (by
    change (z ≫ q) ≫ Y.hom = u
    rw [Category.assoc, hbase, ← Category.assoc, hz, Category.id_comp])
  have hf : s ≫ f.left = t ≫ f.left := by
    change s ≫ z ≫ q = t ≫ z ≫ q
    rw [← Category.assoc, ← hs, Category.assoc, hq, ← Category.assoc, ht, Category.assoc]
  obtain ⟨d, hd, hdunique⟩ := OverKernelPairFactor.over_factor_of_kernelPair u' s t hu f hf
  refine ⟨d, congrArg Over.Hom.left hd, ?_⟩
  intro e he
  exact hdunique e (Over.OverMorphism.ext he)

end

section

/-! The relative square of an actual cartesian family quotient is again
cartesian; its compatible transported-pair relation is its kernel pair. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem kernelPair_of_cartesian_relation {C : Type*} [Category* C]
    {B T X W Y : C} (u : T ⟶ B) (a : X ⟶ T) (b : Y ⟶ B) (q : X ⟶ Y)
    (hcart : IsPullback a q u b) (r : W ⟶ T) (s t : W ⟶ X)
    (hsource : IsPullback r s u (a ≫ u)) (ht : t ≫ a = r)
    (hc : s ≫ q = t ≫ q) : IsKernelPair q s t := by
  have ho : IsPullback (t ≫ a) s u (q ≫ b) := by
    rw [ht, ← hcart.w]
    exact hsource
  exact (ho.of_right hc.symm hcart).flip

theorem family_quotient_pair_cartesian {B T X P : Scheme.{0}}
    (u : T ⟶ B) (a : X ⟶ T) (Y : Over B) (q : X ⟶ Y.left)
    (hcart : IsPullback a q u Y.hom)
    (p₁ p₂ : P ⟶ X) (hp : IsPullback p₁ p₂ a a) :
    ∃ q₂ : P ⟶ (Y ⊗ Y).left,
      q₂ ≫ (fst Y Y).left = p₁ ≫ q ∧
      q₂ ≫ (snd Y Y).left = p₂ ≫ q ∧
      IsPullback (p₁ ≫ a) q₂ u (Y ⊗ Y).hom := by
  let q₂ : P ⟶ (Y ⊗ Y).left := pullback.lift (p₁ ≫ q) (p₂ ≫ q) (by
    rw [Category.assoc, Category.assoc, ← hcart.w, ← Category.assoc, ← Category.assoc, hp.w])
  have h₁ : q₂ ≫ pullback.fst Y.hom Y.hom = p₁ ≫ q := pullback.lift_fst _ _ _
  have h₂ : q₂ ≫ pullback.snd Y.hom Y.hom = p₂ ≫ q := pullback.lift_snd _ _ _
  refine ⟨q₂, h₁, h₂, ?_⟩
  have hw : (p₁ ≫ a) ≫ u = q₂ ≫ (Y ⊗ Y).hom := by
    change _ = q₂ ≫ (pullback.fst Y.hom Y.hom ≫ Y.hom)
    rw [← Category.assoc, h₁, Category.assoc, Category.assoc, hcart.w]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw ?_ ?_ ?_ ?_)
  · intro c
    exact hp.lift
      (hcart.lift c.fst (c.snd ≫ pullback.fst Y.hom Y.hom) (by
        simpa only [Category.assoc, Over.tensorObj_hom, Over.fst_left] using c.condition))
      (hcart.lift c.fst (c.snd ≫ pullback.snd Y.hom Y.hom) (by
        rw [Category.assoc, ← pullback.condition]
        exact c.condition))
      (by rw [hcart.lift_fst, hcart.lift_fst])
  · intro c
    rw [← Category.assoc, hp.lift_fst, hcart.lift_fst]
  · intro c
    apply pullback.hom_ext
    · rw [Category.assoc, h₁, ← Category.assoc, hp.lift_fst, hcart.lift_snd]
    · rw [Category.assoc, h₂, ← Category.assoc, hp.lift_snd, hcart.lift_snd]
  · intro c m hm₁ hm₂
    change m ≫ q₂ = c.snd at hm₂
    apply hp.hom_ext
    · rw [hp.lift_fst]
      apply hcart.hom_ext
      · rw [Category.assoc, hcart.lift_fst]
        exact hm₁
      · rw [Category.assoc, hcart.lift_snd]
        simpa only [Category.assoc, h₁] using congrArg (fun k => k ≫ pullback.fst Y.hom Y.hom) hm₂
    · rw [hp.lift_snd]
      apply hcart.hom_ext
      · rw [Category.assoc, hcart.lift_fst, ← hp.w]
        exact hm₁
      · rw [Category.assoc, hcart.lift_snd]
        simpa only [Category.assoc, h₂] using congrArg (fun k => k ≫ pullback.snd Y.hom Y.hom) hm₂

end

/-! Descend an actual operation between two family quotients from a map
of their effective relations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem family_quotient_operation_descends {B T X P W V : Scheme.{0}}
    (u : T ⟶ B) (a : X ⟶ T) (ap : P ⟶ T)
    (Y Z : Over B) (q : X ⟶ Y.left) (qp : P ⟶ Z.left)
    [EffectiveEpi qp] (hqbase : q ≫ Y.hom = a ≫ u)
    (hpbase : qp ≫ Z.hom = ap ≫ u)
    (s t : W ⟶ X) (hcoeq : s ≫ q = t ≫ q)
    (sp tp : V ⟶ P) (hp : IsKernelPair qp sp tp)
    (m : P ⟶ X) (hm : m ≫ a = ap) (r : V ⟶ W)
    (hs : r ≫ s = sp ≫ m) (ht : r ≫ t = tp ≫ m) :
    ∃! d : Z ⟶ Y, qp ≫ d.left = m ≫ q := by
  let P' : Over B := Over.mk (ap ≫ u)
  let qp' : P' ⟶ Z := Over.homMk qp hpbase
  have : EffectiveEpi qp'.left := inferInstanceAs (EffectiveEpi qp)
  let f : P' ⟶ Y := Over.homMk (m ≫ q) (by
    change (m ≫ q) ≫ Y.hom = ap ≫ u
    rw [Category.assoc, hqbase, ← Category.assoc, hm])
  have hf : sp ≫ f.left = tp ≫ f.left := by
    change sp ≫ m ≫ q = tp ≫ m ≫ q
    rw [← Category.assoc, ← hs, Category.assoc, hcoeq,
      ← Category.assoc, ht, Category.assoc]
  obtain ⟨d, hd, hu⟩ := OverKernelPairFactor.over_factor_of_kernelPair qp' sp tp hp f hf
  exact ⟨d, congrArg Over.Hom.left hd, fun e he => hu e (Over.OverMorphism.ext he)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf
