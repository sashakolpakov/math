/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingGluing

/-! # Tensor Pairing Bilinearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingBilinearity.SheafTensorLocalization

noncomputable section

universe v v' u u'

open _root_.CategoryTheory MonoidalCategory _root_.PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map g)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)]
  {P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (hP : Presheaf.IsSheaf J P.presheaf) (χ : M₁ ⊗ N₁ ⟶ P)

include hP in
lemma pairingSection_add_left {U : Cᵒᵖ} (m m' : M₂.obj U) (n : N₂.obj U) :
    TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ (m + m') n =
      TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n + TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m' n := by
  refine (TensorPairingLocality.SheafTensorLocalization.isPairingSection_unique hP χ (TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ (m + m') n) ?_)
  intro V p a b ha hb
  apply hP.isSeparated _ _ (J.intersection_covering
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m))
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m')))
  rintro W q ⟨hq₁, hq₂⟩
  obtain ⟨a₁, ha₁'⟩ : ∃ a₁ : ↑(M₁.obj (Opposite.op W)),
      f.app (Opposite.op W) a₁ = M₂.map (q ≫ p).op m := hq₁
  obtain ⟨a₂, ha₂'⟩ : ∃ a₂ : ↑(M₁.obj (Opposite.op W)),
      f.app (Opposite.op W) a₂ = M₂.map (q ≫ p).op m' := hq₂
  have hbW : g.app (Opposite.op W) (N₁.map q.op b) = N₂.map (q ≫ p).op n := by
    rw [TensorPairingLocality.SheafTensorLocalization.pom_napp_map g q b, hb, ← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
  have hL : P.presheaf.map q.op (P.map p.op (TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n +
      TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m' n)) =
      χ.app (Opposite.op W) ((a₁ + a₂) ⊗ₜ N₁.map q.op b) := by
    show P.map q.op (P.map p.op (TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n +
      TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m' n)) = _
    rw [← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
    erw [map_add]
    rw [TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m n (q ≫ p) a₁ (N₁.map q.op b) ha₁' hbW,
      TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m' n (q ≫ p) a₂ (N₁.map q.op b) ha₂' hbW]
    exact ((χ.app (Opposite.op W)).hom.map_add _ _).symm.trans
      (congrArg (χ.app (Opposite.op W)) (TensorProduct.add_tmul a₁ a₂ _).symm)
  rw [hL, TensorPairingLocality.SheafTensorLocalization.chi_value χ q a b]
  refine TensorPairingLocality.SheafTensorLocalization.chi_app_congr f g hP χ _ _ _ _ ?_ rfl
  exact (map_add ((f.app (Opposite.op W)).hom) a₁ a₂).trans
    ((congrArg₂ (· + ·) ha₁' ha₂').trans
      ((map_add ((M₂.presheaf.map (q ≫ p).op).hom) m m').symm.trans
        ((TensorPairingLocality.SheafTensorLocalization.pom_map_comp M₂ q p (m + m')).trans
          ((congrArg (M₂.map q.op) ha.symm).trans (TensorPairingLocality.SheafTensorLocalization.pom_napp_map f q a).symm))))

include hP in
lemma pairingSection_smul_left {U : Cᵒᵖ}
    (r : ↑(S.obj U)) (m : M₂.obj U) (n : N₂.obj U) :
    TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ (r • m) n = r • TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n := by
  refine (TensorPairingLocality.SheafTensorLocalization.isPairingSection_unique hP χ (TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ (r • m) n) ?_)
  intro V p a b ha hb
  apply hP.isSeparated _ _
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m))
  intro W q hq₀
  obtain ⟨a₀, ha₀'⟩ : ∃ a₀ : ↑(M₁.obj (Opposite.op W)),
      f.app (Opposite.op W) a₀ = M₂.map (q ≫ p).op m := hq₀
  have hbW : g.app (Opposite.op W) (N₁.map q.op b) = N₂.map (q ≫ p).op n := by
    rw [TensorPairingLocality.SheafTensorLocalization.pom_napp_map g q b, hb, ← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
  set r' : ↑(S.obj (Opposite.op W)) :=
    (S.map (Opposite.op (q ≫ p))).hom r with hr'
  have hL : P.presheaf.map q.op (P.map p.op (r • TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n)) =
      χ.app (Opposite.op W) ((r' • a₀) ⊗ₜ N₁.map q.op b) := by
    show P.map q.op (P.map p.op (r • TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n)) = _
    rw [← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
    erw [P.map_smul]
    rw [TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m n (q ≫ p) a₀ (N₁.map q.op b) ha₀' hbW]
    exact ((χ.app (Opposite.op W)).hom.map_smul r' _).symm.trans
      (congrArg (χ.app (Opposite.op W)) (TensorProduct.smul_tmul' r' a₀ _))
  rw [hL, TensorPairingLocality.SheafTensorLocalization.chi_value χ q a b]
  refine TensorPairingLocality.SheafTensorLocalization.chi_app_congr f g hP χ _ _ _ _ ?_ rfl
  exact (map_smul ((f.app (Opposite.op W)).hom) r' a₀).trans
    ((congrArg (r' • ·) ha₀').trans
      ((M₂.map_smul (q ≫ p).op r m).symm.trans
        ((TensorPairingLocality.SheafTensorLocalization.pom_map_comp M₂ q p (r • m)).trans
          ((congrArg (M₂.map q.op) ha.symm).trans (TensorPairingLocality.SheafTensorLocalization.pom_napp_map f q a).symm))))

include hP in
lemma pairingSection_add_right {U : Cᵒᵖ} (m : M₂.obj U) (n n' : N₂.obj U) :
    TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m (n + n') =
      TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n + TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n' := by
  refine (TensorPairingLocality.SheafTensorLocalization.isPairingSection_unique hP χ (TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m (n + n')) ?_)
  intro V p a b ha hb
  apply hP.isSeparated _ _ (J.intersection_covering
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n')))
  rintro W q ⟨hq₁, hq₂⟩
  obtain ⟨b₁, hb₁'⟩ : ∃ b₁ : ↑(N₁.obj (Opposite.op W)),
      g.app (Opposite.op W) b₁ = N₂.map (q ≫ p).op n := hq₁
  obtain ⟨b₂, hb₂'⟩ : ∃ b₂ : ↑(N₁.obj (Opposite.op W)),
      g.app (Opposite.op W) b₂ = N₂.map (q ≫ p).op n' := hq₂
  have haW : f.app (Opposite.op W) (M₁.map q.op a) = M₂.map (q ≫ p).op m := by
    rw [TensorPairingLocality.SheafTensorLocalization.pom_napp_map f q a, ha, ← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
  have hL : P.presheaf.map q.op (P.map p.op (TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n +
      TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n')) =
      χ.app (Opposite.op W) (M₁.map q.op a ⊗ₜ (b₁ + b₂)) := by
    show P.map q.op (P.map p.op (TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n +
      TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n')) = _
    rw [← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
    erw [map_add]
    rw [TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m n (q ≫ p) (M₁.map q.op a) b₁ haW hb₁',
      TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m n' (q ≫ p) (M₁.map q.op a) b₂ haW hb₂']
    exact ((χ.app (Opposite.op W)).hom.map_add _ _).symm.trans
      (congrArg (χ.app (Opposite.op W)) (TensorProduct.tmul_add _ b₁ b₂).symm)
  rw [hL, TensorPairingLocality.SheafTensorLocalization.chi_value χ q a b]
  refine TensorPairingLocality.SheafTensorLocalization.chi_app_congr f g hP χ _ _ _ _ rfl ?_
  exact (map_add ((g.app (Opposite.op W)).hom) b₁ b₂).trans
    ((congrArg₂ (· + ·) hb₁' hb₂').trans
      ((map_add ((N₂.presheaf.map (q ≫ p).op).hom) n n').symm.trans
        ((TensorPairingLocality.SheafTensorLocalization.pom_map_comp N₂ q p (n + n')).trans
          ((congrArg (N₂.map q.op) hb.symm).trans (TensorPairingLocality.SheafTensorLocalization.pom_napp_map g q b).symm))))

include hP in
lemma pairingSection_smul_right {U : Cᵒᵖ}
    (r : ↑(S.obj U)) (m : M₂.obj U) (n : N₂.obj U) :
    TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m (r • n) = r • TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n := by
  refine (TensorPairingLocality.SheafTensorLocalization.isPairingSection_unique hP χ (TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m (r • n)) ?_)
  intro V p a b ha hb
  apply hP.isSeparated _ _
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
  intro W q hq₀
  obtain ⟨b₀, hb₀'⟩ : ∃ b₀ : ↑(N₁.obj (Opposite.op W)),
      g.app (Opposite.op W) b₀ = N₂.map (q ≫ p).op n := hq₀
  have haW : f.app (Opposite.op W) (M₁.map q.op a) = M₂.map (q ≫ p).op m := by
    rw [TensorPairingLocality.SheafTensorLocalization.pom_napp_map f q a, ha, ← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
  set r' : ↑(S.obj (Opposite.op W)) :=
    (S.map (Opposite.op (q ≫ p))).hom r with hr'
  have hL : P.presheaf.map q.op (P.map p.op (r • TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n)) =
      χ.app (Opposite.op W) (M₁.map q.op a ⊗ₜ (r' • b₀)) := by
    show P.map q.op (P.map p.op (r • TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n)) = _
    rw [← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
    erw [P.map_smul]
    rw [TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m n (q ≫ p) (M₁.map q.op a) b₀ haW hb₀']
    exact ((χ.app (Opposite.op W)).hom.map_smul r' _).symm.trans
      (congrArg (χ.app (Opposite.op W)) (TensorProduct.tmul_smul r' _ b₀).symm)
  rw [hL, TensorPairingLocality.SheafTensorLocalization.chi_value χ q a b]
  refine TensorPairingLocality.SheafTensorLocalization.chi_app_congr f g hP χ _ _ _ _ rfl ?_
  exact (map_smul ((g.app (Opposite.op W)).hom) r' b₀).trans
    ((congrArg (r' • ·) hb₀').trans
      ((N₂.map_smul (q ≫ p).op r n).symm.trans
        ((TensorPairingLocality.SheafTensorLocalization.pom_map_comp N₂ q p (r • n)).trans
          ((congrArg (N₂.map q.op) hb.symm).trans (TensorPairingLocality.SheafTensorLocalization.pom_napp_map g q b).symm))))

include hP in
lemma pairingSection_map {U : Cᵒᵖ} {V : C} (p : V ⟶ U.unop)
    (m : M₂.obj U) (n : N₂.obj U) :
    P.map p.op (TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m n) =
      TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ
        (show ↑(M₂.obj (Opposite.op V)) from M₂.map p.op m)
        (show ↑(N₂.obj (Opposite.op V)) from N₂.map p.op n) := by
  refine TensorPairingLocality.SheafTensorLocalization.isPairingSection_unique hP χ ?_
    (TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ
      (show ↑(M₂.obj (Opposite.op V)) from M₂.map p.op m)
      (show ↑(N₂.obj (Opposite.op V)) from N₂.map p.op n))
  intro W q a b ha hb
  rw [← TensorPairingLocality.SheafTensorLocalization.pom_map_comp]
  exact TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ m n (q ≫ p) a b
    (ha.trans (TensorPairingLocality.SheafTensorLocalization.pom_map_comp M₂ q p m).symm) (hb.trans (TensorPairingLocality.SheafTensorLocalization.pom_map_comp N₂ q p n).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingBilinearity.SheafTensorLocalization
