import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.TensorEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.GlobalGeneration

/-! # Unit Degree Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! All sufficiently large powers of an ample line bundle give closed
embeddings. In particular an arbitrarily large unit degree can be chosen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (.of R)}
    {L : Line.Bundles.LineBundle X}

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.allPowers_eventually_generated
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m → Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (L.tensorPower m).sheaf := by
  classical
  have h (r : Fin E.degree) : ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators
        (Tensor.ProductSheaf.tensorModule (L.tensorPower r.val).sheaf (L.tensorPower (m * E.degree)).sheaf) := by
    let : (L.tensorPower r.val).sheaf.IsQuasicoherent := (L.tensorPower r.val).isQuasicoherent
    let : (L.tensorPower r.val).sheaf.IsFiniteType := (L.tensorPower r.val).isFiniteType
    exact E.tensorPowers_eventually_hasFiniteGlobalGenerators (L.tensorPower r.val).sheaf
  choose B hB using h
  let b := Finset.univ.sup B
  refine ⟨b * E.degree, fun m hm => ?_⟩
  let r : Fin E.degree := ⟨m % E.degree, Nat.mod_lt _ E.degree_pos⟩
  have hb : B r ≤ m / E.degree := by
    apply (Finset.le_sup (f := B) (Finset.mem_univ r)).trans
    exact (Nat.le_div_iff_mul_le E.degree_pos).mpr hm
  have hgen := hB r (m / E.degree) hb
  have he : r.val + m / E.degree * E.degree = m := Nat.mod_add_div' m E.degree
  exact hgen.of_iso ((L.tensorPowerAddIso r.val (m / E.degree * E.degree)).symm ≪≫
    eqToIso (congrArg (fun n => (L.tensorPower n).sheaf) he))

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.allPowers_eventually_embedding
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      ∃ F : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f, F.degree = m := by
  obtain ⟨B, hB⟩ := E.allPowers_eventually_generated
  refine ⟨E.degree + B, fun m hm => ?_⟩
  have hdegree : E.degree ≤ m := (Nat.le_add_right _ _).trans hm
  have hB' : B ≤ m - E.degree := by omega
  obtain ⟨F, hF⟩ := E.exists_addGeneratedPower (m - E.degree) (hB _ hB')
  exact ⟨F, hF.trans (Nat.add_sub_of_le hdegree)⟩

theorem Line.Bundles.LineBundle.IsAmple.exists_powerDegreeEmbedding [IsProper f]
    (hL : L.IsAmple) (q : ℕ) (hq : 1 < q) :
    ∃ (k : ℕ) (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f), E.degree = q ^ k := by
  obtain ⟨E⟩ := hL.exists_powerProjectiveEmbedding f
  obtain ⟨B, hB⟩ := E.allPowers_eventually_embedding
  have hbound : B ≤ q ^ B := Nat.le_of_lt (Nat.lt_pow_self hq)
  obtain ⟨F, hF⟩ := hB (q ^ B) hbound
  exact ⟨B, F, hF⟩

theorem Line.Bundles.LineBundle.IsAmple.exists_unitDegreeEmbedding [IsProper f]
    (hL : L.IsAmple) (q : ℕ) (hq : 1 < q) (hqu : IsUnit (q : R)) :
    ∃ E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f, IsUnit (E.degree : R) := by
  obtain ⟨k, E, hE⟩ := hL.exists_powerDegreeEmbedding (f := f) q hq
  exact ⟨E, by rw [hE, Nat.cast_pow]; exact hqu.pow k⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
