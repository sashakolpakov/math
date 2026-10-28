import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveComparison

/-! # Projective Quasi Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ProjectiveQuasiIso

noncomputable section

/-! Quasi-isomorphisms between bounded above nonnegative complexes of projective objects are homotopy equivalences, hence remain quasi-isomorphisms under every additive functor. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w t
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem boundedProjective_extend_isKProjective
    (K : CochainComplex C ℕ) [∀ q, Projective (K.X q)]
    (N : ℕ) (hN : ∀ q, N ≤ q → IsZero (K.X q)) :
    ProjectiveBasic.CochainComplex.IsKProjective (K.extend ComplexShape.embeddingUpNat) := by
  let E : CochainComplex C ℤ := K.extend ComplexShape.embeddingUpNat
  have : _root_.CochainComplex.IsStrictlyLE E (N : ℤ) := by
    apply (CochainComplex.isStrictlyLE_iff E (N : ℤ)).mpr
    intro q hq
    by_cases he : ∃ n, ComplexShape.embeddingUpNat.f n = q
    · obtain ⟨n, rfl⟩ := he
      have hn : N ≤ n := by
        change (N : ℤ) < (n : ℤ) at hq
        omega
      exact (K.extendXIso ComplexShape.embeddingUpNat rfl).isZero_iff.mpr (hN n hn)
    · exact K.isZero_extend_X ComplexShape.embeddingUpNat q (by simpa using he)
  exact ProjectiveBasic.CochainComplex.isKProjective_of_projective E (N : ℤ)

theorem boundedProjective_quasiIso_homotopyEquivalence
    {K L : CochainComplex C ℕ} [∀ q, Projective (K.X q)] [∀ q, Projective (L.X q)]
    (hK : ∃ N, ∀ q, N ≤ q → IsZero (K.X q))
    (hL : ∃ N, ∀ q, N ≤ q → IsZero (L.X q))
    (f : K ⟶ L) [QuasiIso f] : HomologicalComplex.homotopyEquivalences C (.up ℕ) f := by
  obtain ⟨NK, hNK⟩ := hK
  obtain ⟨NL, hNL⟩ := hL
  have : ProjectiveBasic.CochainComplex.IsKProjective (K.extend ComplexShape.embeddingUpNat) :=
    boundedProjective_extend_isKProjective K NK hNK
  have : ProjectiveBasic.CochainComplex.IsKProjective (L.extend ComplexShape.embeddingUpNat) :=
    boundedProjective_extend_isKProjective L NL hNL
  have hf : QuasiIso (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff f ComplexShape.embeddingUpNat).mpr inferInstance
  exact (HomologicalComplex.homotopyEquivalences_extendMap_iff f ComplexShape.embeddingUpNat).mp
    ((ProjectiveBasic.CochainComplex.IsKProjective.quasiIso_iff
      (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)).mp hf)

theorem boundedProjective_map_quasiIso
    {K L : CochainComplex C ℕ} [∀ q, Projective (K.X q)] [∀ q, Projective (L.X q)]
    (hK : ∃ N, ∀ q, N ≤ q → IsZero (K.X q))
    (hL : ∃ N, ∀ q, N ≤ q → IsZero (L.X q))
    (f : K ⟶ L) [QuasiIso f]
    {D : Type w} [Category.{t} D] [Abelian D] (F : C ⥤ D) [F.Additive] :
    QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map f) := by
  obtain ⟨e, rfl⟩ := boundedProjective_quasiIso_homotopyEquivalence hK hL f
  exact homotopyEquivalences_le_quasiIso D (.up ℕ) _
    (F.mapHomotopyEquiv e).homotopyEquivalences_hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ProjectiveQuasiIso
