import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterGeometry

/-! # Point Parameter Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterSource

noncomputable section

/-! The quotient parameters generate the actual section ideal on
the smooth source as well as the concatenated ambient point ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem quotient_generators {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    (f : A →+* B) (hf : Function.Surjective f) (ε : B →+* R)
    {c m : ℕ} (s : Fin c → A) (t : Fin m → A)
    (hs : Ideal.span (Set.range s) = RingHom.ker f)
    (hst : Ideal.span (Set.range (Fin.append s t)) = RingHom.ker (ε.comp f)) :
    Ideal.span (Set.range (fun j => f (t j))) = RingHom.ker ε := by
  have hk : (RingHom.ker f).map f = ⊥ := by
    apply le_antisymm _ bot_le
    rw [Ideal.map_le_iff_le_comap]
    exact le_rfl
  have h := congrArg (Ideal.map f) hst
  rw [CompositeSectionKernel.range_append, Ideal.span_union, Ideal.map_sup, hs, hk,
    bot_sup_eq, Ideal.map_span, ← Set.range_comp, ← RingHom.comap_ker,
    Ideal.map_comap_of_surjective f hf] at h
  exact h

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) [IsClosedImmersion f.left]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (U : Y.left.Opens) (hU : IsAffineOpen U) (hsU : ⊤ ≤ s ⁻¹ᵁ (f.left ⁻¹ᵁ U))
  (σ : Type u) [Fintype σ] [Algebra (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  {c m : ℕ} (a : Fin c → Γ(Y.left, U)) (e : Fin m ≃ σ)
  (ha : Ideal.span (Set.range a) = f.left.ker.ideal ⟨U, hU⟩)
  (r : Γ(Y.left, U))
  (D : PointParameterNeighborhood.Data R X Y f s hs U hsU σ a e r)

include ha in
omit [Fintype σ] [IsScalarTower R (MvPolynomial σ R) ↑(SmoothClosedSections.ring R X (Over.Hom.left f ⁻¹ᵁ U))] [Algebra.Etale (MvPolynomial σ R) ↑(SmoothClosedSections.ring R X (Over.Hom.left f ⁻¹ᵁ U))] in
theorem kernel :
    Ideal.span (Set.range (PointParameterNeighborhood.quotientParameter R X Y f s hs U hsU σ e r)) =
      RingHom.ker (SectionEvaluation.evaluation R X s hs
        (f.left ⁻¹ᵁ Y.left.basicOpen r) D.contains).toRingHom := by
  change (Ideal.span (Set.range (fun j =>
    PointParameterNeighborhood.quotientParameter R X Y f s hs U hsU σ e r j)) :
      Ideal Γ(X.left, f.left ⁻¹ᵁ Y.left.basicOpen r)) = _
  have hnormal : Ideal.span (Set.range (IdealSheafPrincipalEquations.sequence U r a)) =
      RingHom.ker (f.left.app (Y.left.basicOpen r)).hom := by
    have h := IdealSheafPrincipalEquations.generates f.left.ker U hU r a ha
    simpa only [Scheme.Hom.ker_apply] using h
  have h := quotient_generators (f.left.app (Y.left.basicOpen r)).hom
    (f.left.app_surjective _ (hU.basicOpen r))
    (SectionEvaluation.evaluation R X s hs
      (f.left ⁻¹ᵁ Y.left.basicOpen r) D.contains).toRingHom
    (IdealSheafPrincipalEquations.sequence U r a) D.parameter hnormal D.kernel
  simpa only [D.lift] using h

include ha D in
omit [Fintype σ] [IsScalarTower R (MvPolynomial σ R) ↑(SmoothClosedSections.ring R X (Over.Hom.left f ⁻¹ᵁ U))] [Algebra.Etale (MvPolynomial σ R) ↑(SmoothClosedSections.ring R X (Over.Hom.left f ⁻¹ᵁ U))] in
theorem ideal [IsClosedImmersion s] :
    Ideal.span (Set.range (PointParameterNeighborhood.quotientParameter R X Y f s hs U hsU σ e r)) =
      s.ker.ideal ⟨f.left ⁻¹ᵁ Y.left.basicOpen r, (hU.basicOpen r).preimage f.left⟩ :=
  (PointParameterSource.kernel R X Y f s hs U hU hsU σ a e ha r D).trans
    (SectionEvaluation.kernel R X s hs (f.left ⁻¹ᵁ Y.left.basicOpen r)
      D.contains ((hU.basicOpen r).preimage f.left))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterSource
