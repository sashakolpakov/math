import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenseOpen
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperLocal

/-! # Chow Embedding Closed -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ChowEmbeddingClosed.Construction.ChowEmbedding

noncomputable section

/-! The closed-embedding step of Chow's construction: a proper graph
closure embeds in the product of its chart compactifications. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u v

theorem closed {Z X P W : Scheme.{u}} [IsReduced Z] [X.IsSeparated]
    (q : Z ⟶ X) (g : Z ⟶ P) [IsProper g] [IsImmersion (prod.lift q g)]
    {ι : Type v} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (Q : ι → Scheme.{u}) [∀ i, (Q i).IsSeparated]
    (c : ∀ i, (U i).toScheme ⟶ Q i) [∀ i, IsOpenImmersion (c i)]
    (r : ∀ i, P ⟶ Q i)
    (j : W ⟶ Z) [IsDominant j] (w : ∀ i, W ⟶ (U i).toScheme)
    (hq : ∀ i, j ≫ q = w i ≫ (U i).ι)
    (hg : ∀ i, j ≫ g ≫ r i = w i ≫ c i) : IsClosedImmersion g := by
  let V : ι → P.Opens := fun i => r i ⁻¹ᵁ (c i).opensRange
  have he (i) : q ⁻¹ᵁ U i = g ⁻¹ᵁ V i :=
    DenseOpen.Construction.DenseOpenFactorization.preimage_eq q (g ≫ r i) (U i) (c i) j (w i) (hq i) (hg i)
  apply ProperLocal.Construction.ProperLocalImmersion.closed_of_chart_cover g V
  · intro z
    obtain ⟨i, hi⟩ := hU (q z)
    refine ⟨i, ?_⟩
    change z ∈ g ⁻¹ᵁ V i
    rw [← he i]
    exact hi
  · intro i
    have hrel := DenseOpen.Construction.DenseOpenFactorization.factor q (g ≫ r i) (U i) (c i) j (w i) (hq i) (hg i)
    let A := q ⁻¹ᵁ U i
    have hp : IsImmersion (prod.lift (q ∣_ U i ≫ (U i).ι) (A.ι ≫ g)) := by
      have hpair : prod.lift (q ∣_ U i ≫ (U i).ι) (A.ι ≫ g) = A.ι ≫ prod.lift q g := by
        rw [morphismRestrict_ι, prod.comp_lift]
      rw [hpair]
      infer_instance
    have hi : IsImmersion (A.ι ≫ g) :=
      ProperLocal.Construction.ProperLocalImmersion.immersion_of_open_coordinate (q ∣_ U i) (A.ι ≫ g)
        (U i).ι (c i) (r i) (by simpa only [Category.assoc] using hrel)
    exact (congrArg (fun B : Z.Opens => IsImmersion (B.ι ≫ g)) (he i)).mp hi

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ChowEmbeddingClosed.Construction.ChowEmbedding
