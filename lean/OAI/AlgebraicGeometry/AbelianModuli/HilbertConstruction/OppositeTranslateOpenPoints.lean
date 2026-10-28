import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ClosedIntegrality

/-! # Opposite Translate Open Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OppositeTranslateOpenPoints

noncomputable section

/-! A nonempty open in an abelian variety admits a pair of opposite
rational translates through any prescribed rational point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem overIso_preimage_open_nonempty {S : Scheme.{u}} {X : Over S}
    (e : X ≅ X) (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    (e.hom.left ⁻¹ᵁ U : Set X.left).Nonempty := by
  obtain ⟨x, hx⟩ := hU
  refine ⟨e.inv.left x, ?_⟩
  have he := congrArg (fun f : X ⟶ X => f.left x) e.inv_hom_id
  change e.hom.left (e.inv.left x) = x at he
  change e.hom.left (e.inv.left x) ∈ U
  exact he.symm ▸ hx

namespace AbelianScheme
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.exists_oppositeTranslations_mem_open
    (U : A.scheme.left.Opens) (hU : (U : Set A.scheme.left).Nonempty)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    ∃ a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme,
      (A.basePointTranslation a).left (x.left (IsLocalRing.closedPoint K)) ∈ U ∧
      (A.basePointTranslation a⁻¹).left (x.left (IsLocalRing.closedPoint K)) ∈ U := by
  have : IrreducibleSpace A.scheme.left := A.irreducible_overAlgClosed
  let E := A.basePointTranslationIso x
  let F : A.scheme ≅ A.scheme := asIso ι[A.scheme] ≪≫ E
  let V : A.scheme.left.Opens := E.hom.left ⁻¹ᵁ U
  let W : A.scheme.left.Opens := F.hom.left ⁻¹ᵁ U
  have hi : (V ⊓ W : Set A.scheme.left).Nonempty :=
    nonempty_preirreducible_inter V.isOpen W.isOpen
      (overIso_preimage_open_nonempty E U hU) (overIso_preimage_open_nonempty F U hU)
  let T : A.scheme.left.Opens := V ⊓ W
  have : Nonempty T.toScheme := ⟨⟨hi.choose, hi.choose_spec⟩⟩
  obtain ⟨q, hq⟩ := ClosedRationalPoints.nonempty_locallyFiniteType_exists_section (T.ι ≫ A.scheme.hom)
  let a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme :=
    Over.homMk (q ≫ T.ι) (by
      change (q ≫ T.ι) ≫ A.scheme.hom = 𝟙 (Spec (.of K))
      simpa only [Category.assoc] using hq)
  have ha : E.hom.left (a.left (IsLocalRing.closedPoint K)) ∈ U ∧
      F.hom.left (a.left (IsLocalRing.closedPoint K)) ∈ U :=
    (q (IsLocalRing.closedPoint K)).property
  have hp : a ≫ E.hom = x ≫ A.basePointTranslation a := by
    change a ≫ A.basePointTranslation x = x ≫ A.basePointTranslation a
    simp only [Abelian.Schemes.AbelianScheme.point_comp_basePointTranslation]
    exact mul_comm _ _
  have hm : a ≫ F.hom = x ≫ A.basePointTranslation a⁻¹ := by
    change a ≫ (ι[A.scheme] ≫ A.basePointTranslation x) = _
    rw [← Category.assoc, ← Hom.inv_def]
    simp only [Abelian.Schemes.AbelianScheme.point_comp_basePointTranslation]
    exact mul_comm _ _
  have hp' := congrArg (fun f : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme =>
    f.left (IsLocalRing.closedPoint K)) hp
  have hm' := congrArg (fun f : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme =>
    f.left (IsLocalRing.closedPoint K)) hm
  change E.hom.left (a.left (IsLocalRing.closedPoint K)) =
    (A.basePointTranslation a).left (x.left (IsLocalRing.closedPoint K)) at hp'
  change F.hom.left (a.left (IsLocalRing.closedPoint K)) =
    (A.basePointTranslation a⁻¹).left (x.left (IsLocalRing.closedPoint K)) at hm'
  exact ⟨a, hp' ▸ ha.1, hm' ▸ ha.2⟩

end AbelianScheme

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OppositeTranslateOpenPoints
