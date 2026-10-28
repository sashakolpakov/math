import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GenericLift

/-! # Dense Open -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenseOpen.Construction.DenseOpenFactorization

noncomputable section

/-! Equalities on a dense graph extend to chart relations on its reduced closure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

theorem factor {Z X Q W : Scheme.{u}} [IsReduced Z] [Q.IsSeparated]
    (q : Z ⟶ X) (b : Z ⟶ Q) (U : X.Opens) (c : U.toScheme ⟶ Q)
    (j : W ⟶ Z) [IsDominant j] (w : W ⟶ U.toScheme)
    (hj : j ≫ q = w ≫ U.ι) (hb : j ≫ b = w ≫ c) :
    q ∣_ U ≫ c = (q ⁻¹ᵁ U).ι ≫ b := by
  have hr : Set.range j ⊆ Set.range (q ⁻¹ᵁ U).ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨j x, ?_⟩, rfl⟩
    change q (j x) ∈ U
    have he := congrArg (fun f : W ⟶ X => f x) hj
    exact he ▸ (w x).2
  let a := IsOpenImmersion.lift (q ⁻¹ᵁ U).ι j hr
  have ha : a ≫ q ∣_ U = w := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      IsOpenImmersion.lift_fac, hj]
  have : IsDominant a := GenericLift.Construction.GenericLiftRestriction.dominant_lift _ _ hr
  apply ext_of_isDominant_of_isSeparated (terminal.from Q) (Subsingleton.elim _ _) a
  rw [← Category.assoc, ha, ← Category.assoc, IsOpenImmersion.lift_fac, hb]

theorem preimage_eq {Z X Q W : Scheme.{u}} [IsReduced Z] [X.IsSeparated] [Q.IsSeparated]
    (q : Z ⟶ X) (b : Z ⟶ Q) (U : X.Opens) (c : U.toScheme ⟶ Q) [IsOpenImmersion c]
    (j : W ⟶ Z) [IsDominant j] (w : W ⟶ U.toScheme)
    (hj : j ≫ q = w ≫ U.ι) (hb : j ≫ b = w ≫ c) :
    q ⁻¹ᵁ U = b ⁻¹ᵁ c.opensRange := by
  let e : U.toScheme ≅ c.opensRange.toScheme :=
    IsOpenImmersion.isoOfRangeEq c c.opensRange.ι (by simp)
  have he : e.hom ≫ c.opensRange.ι = c := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hw : j ≫ b = (w ≫ e.hom) ≫ c.opensRange.ι := by rw [Category.assoc, he, hb]
  have hw' : j ≫ q = (w ≫ e.hom) ≫ e.inv ≫ U.ι := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, hj]
  have h₁ := factor q b U c j w hj hb
  have h₂ := factor b q c.opensRange (e.inv ≫ U.ι) j (w ≫ e.hom) hw hw'
  apply le_antisymm
  · intro z hz
    let z' : (q ⁻¹ᵁ U).toScheme := ⟨z, hz⟩
    have h := congrArg (fun f : (q ⁻¹ᵁ U).toScheme ⟶ Q => f z') h₁
    change b z ∈ Set.range c
    exact ⟨(q ∣_ U) z', h⟩
  · intro z hz
    let z' : (b ⁻¹ᵁ c.opensRange).toScheme := ⟨z, hz⟩
    have h := congrArg (fun f : (b ⁻¹ᵁ c.opensRange).toScheme ⟶ X => f z') h₂
    change q z ∈ U
    change U.ι (e.inv ((b ∣_ c.opensRange) z')) = q z at h
    exact h ▸ (e.inv ((b ∣_ c.opensRange) z')).2

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenseOpen.Construction.DenseOpenFactorization
