import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DomainRank

/-! # Integral Degree -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntegralDegree.Construction.Schemes

noncomputable section

/-! Composition of finite flat degrees on integral schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- The degree tower law on integral schemes, proved on an actual affine neighborhood. -/
theorem integral_finrank_comp {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f] [Surjective f]
    [IsFinite g] [Flat g] (y : Y) :
    (f ≫ g).finrank (g y) = g.finrank (g y) * f.finrank y := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show g y ∈ (⊤ : Z.Opens) from trivial)
  let V : Y.Opens := g ⁻¹ᵁ U
  let W : X.Opens := f ⁻¹ᵁ V
  have : IsAffine U := hU
  have hV : IsAffineOpen V := hU.preimage g
  have : IsAffine V := hV
  have : IsAffine W := hV.preimage f
  have : Nonempty U := ⟨⟨g y, hy⟩⟩
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  obtain ⟨x, hx⟩ := f.surjective y
  have : Nonempty W := ⟨⟨x, by change g (f x) ∈ U; rwa [hx]⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let f' := f ∣_ V
  let g' := g ∣_ U
  have : Surjective f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f V).flip (inferInstanceAs (Surjective f))
  have sq : IsPullback W.ι (f' ≫ g') (f ≫ g) U.ι :=
    (isPullback_morphismRestrict f V).flip.paste_vert (isPullback_morphismRestrict g U).flip
  let y' : V.toScheme := ⟨y, hy⟩
  let z' : U.toScheme := ⟨g y, hy⟩
  have h := DomainRank.Construction.Schemes.affine_finrank_comp f' g' y' z'
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq z',
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict g U).flip z',
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict f V).flip y'] at h
  exact h

/-- Commuting finite flat endomorphisms have equal degree across a finite flat surjection. -/
theorem endomorphism_finrank_eq_of_commuting
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    [IsFinite f] [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    [IsFinite a] [Flat a] [Surjective a] [IsFinite b] [Flat b]
    [LocallyOfFinitePresentation b]
    (h : a ≫ f = f ≫ b) (x : X) : a.finrank x = b.finrank (f x) := by
  have ha := integral_finrank_comp a f x
  have hb := integral_finrank_comp f b (f x)
  have hdeg : b.finrank (f x) = b.finrank (b (f x)) :=
    b.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
  have hcomp : (f ≫ b).finrank (f x) = (f ≫ b).finrank (b (f x)) := by
    have : LocallyOfFinitePresentation (f ≫ b) := by infer_instance
    exact (f ≫ b).isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
  rw [h, hcomp, hb, ← hdeg] at ha
  exact Nat.eq_of_mul_eq_mul_left (f.one_le_finrank_iff_surjective.mpr inferInstance (f x))
    (ha.symm.trans (Nat.mul_comm _ _))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntegralDegree.Construction.Schemes
