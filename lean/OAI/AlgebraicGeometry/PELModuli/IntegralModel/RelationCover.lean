import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoverUnitBaseChange

/-! # Relation Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RelationCover

noncomputable section

/-! Relation-invariant affine covers away from one coefficient become
actual invariant covers whenever that coefficient becomes a unit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem baseChange_point_avoids_unit {R R' : Type} [CommRing R] [CommRing R']
    (φ : R →+* R') (r : R) (hr : IsUnit (φ r)) (X : Over (Spec (.of R)))
    (x : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left) :
    r ∉ (X.hom (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)) x)).asIdeal := by
  let b := Spec.map (CommRingCat.ofHom φ)
  intro h
  have he : X.hom (pullback.fst X.hom b x) = b (pullback.snd X.hom b x) :=
    congrArg (fun f : ((Over.pullback b).obj X).left ⟶ Spec (.of R) => f x) pullback.condition
  have h' : φ r ∈ (pullback.snd X.hom b x).asIdeal :=
    (congrArg (fun p : Spec (.of R) => r ∈ p.asIdeal) he).mp h
  exact (pullback.snd X.hom b x).isPrime.ne_top
    ((pullback.snd X.hom b x).asIdeal.eq_top_of_isUnit_mem h' hr)

theorem relation_affine_cover_baseChange_of_unit
    {R R' : Type} [CommRing R] [CommRing R'] {I : Type}
    (X Z : Over (Spec (.of R))) (a b : Z ⟶ X) (V : I → X.left.Opens) (r : R)
    (hV : ∀ i, IsAffineOpen (V i))
    (hcover : ∀ x : X.left, r ∉ (X.hom x).asIdeal → ∃ i, x ∈ V i)
    (hInv : ∀ i (z : Z.left), r ∉ (Z.hom z).asIdeal → (a.left z ∈ V i ↔ b.left z ∈ V i))
    (φ : R →+* R') (hunit : IsUnit (φ r)) :
    let c := Spec.map (CommRingCat.ofHom φ)
    let q := pullback.fst X.hom c
    (∀ i, IsAffineOpen (q ⁻¹ᵁ V i)) ∧ (⨆ i, q ⁻¹ᵁ V i) = ⊤ ∧
      (∀ i, ((Over.pullback c).map a).left ⁻¹ᵁ (q ⁻¹ᵁ V i) =
        ((Over.pullback c).map b).left ⁻¹ᵁ (q ⁻¹ᵁ V i)) := by
  let c := Spec.map (CommRingCat.ofHom φ)
  let q := pullback.fst X.hom c
  let qZ := pullback.fst Z.hom c
  have : IsAffineHom q := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback X.hom c).flip (inferInstanceAs (IsAffineHom c))
  refine ⟨fun i => (hV i).preimage q, ?_, ?_⟩
  · apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi⟩ := hcover (q x) (baseChange_point_avoids_unit φ r hunit X x)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    ext z
    have hm (f : Z ⟶ X) : q (((Over.pullback c).map f).left z) = f.left (qZ z) :=
      congrArg (fun f : ((Over.pullback c).obj Z).left ⟶ X.left => f z) (pullback.lift_fst _ _ _)
    change q (((Over.pullback c).map a).left z) ∈ V i ↔ q (((Over.pullback c).map b).left z) ∈ V i
    rw [hm a, hm b]
    exact hInv i (qZ z) (baseChange_point_avoids_unit φ r hunit Z z)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RelationCover
