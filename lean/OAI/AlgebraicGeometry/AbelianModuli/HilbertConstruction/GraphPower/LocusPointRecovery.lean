import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementTransportIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PowerEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelIso

/-! # Locus Point Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPointRecovery.GraphPowerLocusPresentation

noncomputable section

/-! An original polarized family with a recovered full-level projective
fiber lifts to any presentation of its graph-power locus. The resulting
universal fiber is compared by an original level-preserving isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem transportEnhancement_class
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    {F G : Level.Data.AbelianSchemeWithFullLevel g N S}
    {L : Line.Bundles.LineBundle F.abelian.scheme.left} {M : Line.Bundles.LineBundle G.abelian.scheme.left} {d : ℕ}
    (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d)
    (e : F.abelian.scheme ≅ G.abelian.scheme) [IsMonHom e.hom]
    (he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L)
    (hl : F.level.transport e = G.level) :
    D.object.classOf = (D.transportFamily (G := G) e he).object.classOf :=
  (D.object.classOf_eq_iff _).mpr ⟨D.transportFamilyModuliIso (G := G) e he hl⟩

variable {R : Type} [CommRing R]
    {M : Over (Spec (.of R))} [IsNoetherian M.left] {g N d : ℕ}
    {F : Level.Data.AbelianSchemeWithFullLevel g N M.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme} {δ : Fin g → ℕ}
    (Q : LocusPresentation.GraphPowerLocusPresentation M F P d δ)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation.GraphPowerLocusPresentation.exists_point_recovery (hd : 0 < d) (hδ : ∀ i, 0 < δ i)
    {T : Over (Spec (.of R))} (x : T ⟶ M)
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (e : A.abelian.scheme ≅ (F.abelian.pullback x.left).scheme) [IsMonHom e.hom]
    (hl : A.level.transport e = F.level.pullback x.left)
    (hpower : (((P.baseChange x.left).ampleLineBundle).pullback e.hom.left).sheaf ≅
      (A.graphBundle.tensorPower d).sheaf) :
    ∃ z : T ⟶ Q.parameter,
      z ≫ Q.inclusion = x ∧
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A (Q.universalFamily.pullback z.left)) := by
  let F₀ : Level.Data.AbelianSchemeWithFullLevel g N T.left := ⟨A.abelian, A.level⟩
  let H₀ : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F₀ (A.graphBundle.tensorPower d) d :=
    ⟨A.dual, A.polarization, ⟨Iso.refl _⟩⟩
  let e₀ : F₀.abelian.scheme ≅ (F.pullback x.left).abelian.scheme := e
  let : IsMonHom e₀.hom := inferInstanceAs (IsMonHom e.hom)
  have hl₀ : F₀.level.transport e₀ = (F.pullback x.left).level := hl
  have h₀ : H₀.object = A := rfl
  have he : Line.Bundles.LineBundle.pullbackClass e.hom.left
      (Line.Bundles.LineBundle.classOf (P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left))) =
        Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d) :=
    Quotient.sound ⟨(Scheme.Modules.pullback e.hom.left).mapIso
      (P.baseChangeTwistingBundleIso x.left).symm ≪≫ hpower⟩
  let H₁ : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback x.left)
      (P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left)) d :=
    H₀.transportFamily (F := F₀) (G := F.pullback x.left)
      (M := P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left)) e₀ he
  have h₁ : H₀.object.classOf = H₁.object.classOf :=
    transportEnhancement_class (F := F₀) (G := F.pullback x.left)
      (M := P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left)) H₀ e₀ he hl₀
  let H := PolarizationEnhancementData.GraphPowerPolarizationEnhancement.normalizeParameter
    (F := F) (L := P.ampleLineBundle) x.left H₁
  have hnorm : H.object = H₁.object :=
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement.normalizeParameter_object
      (F := F) (L := P.ampleLineBundle) x.left H₁
  have hA : A.classOf = H.object.classOf :=
    (congrArg (fun B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left => B.classOf) h₀).symm.trans
      (h₁.trans (congrArg
        (fun B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left => B.classOf) hnorm).symm)
  obtain ⟨z, hz⟩ := (Q.lifts_iff T x).mpr ⟨H⟩
  have hclass := Q.universalFamily_classifies hd hδ z
  rw [hz] at hclass
  exact ⟨z, hz, (A.classOf_eq_iff (Q.universalFamily.pullback z.left)).mp
    (hA.trans (hclass H).symm)⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation.GraphPowerLocusPresentation.exists_point_recovery_of_embedding (hd : 0 < d) (hδ : ∀ i, 0 < δ i)
    {T : Over (Spec (.of R))} (x : T ⟶ M)
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hE : E.degree = d)
    (e : A.abelian.scheme ≅ (F.abelian.pullback x.left).scheme) [hegroup : IsMonHom e.hom]
    (hl : A.level.transport e = F.level.pullback x.left)
    (hn : P.dimension = E.projectivePresentation.dimension)
    (he : HEq (e.hom.left ≫ (P.baseChange x.left).embedding.left)
      E.projectivePresentation.embedding.left) :
    ∃ z : T ⟶ Q.parameter,
      z ≫ Q.inclusion = x ∧
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A (Q.universalFamily.pullback z.left)) := by
  let powerIso := P.baseChangeSectionRecovery E.projectivePresentation E.power E.sectionData
    x.left e hn he ≪≫ E.canonicalDegreeIso d hE
  exact Q.exists_point_recovery hd hδ x A e hl powerIso

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation.GraphPowerLocusPresentation.exists_point_recovery_of_fullLevel (hd : 0 < d) (hδ : ∀ i, 0 < δ i)
    {T : Over (Spec (.of R))} (x : T ⟶ M)
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hE : E.degree = d)
    (k : A.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left P.dimension)
    (hrec : Embedded.LevelIso.EmbeddedFullLevelRecovery A.abelian A.level (F.pullback x.left)
      k (Embedded.LevelIso.abelianProjectiveBaseChangeEmbedding F.abelian P x.left))
    (hn : P.dimension = E.projectivePresentation.dimension)
    (hk : HEq k.left E.projectivePresentation.embedding.left) :
    ∃ z : T ⟶ Q.parameter,
      z ≫ Q.inclusion = x ∧
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A (Q.universalFamily.pullback z.left)) := by
  obtain ⟨e, hgroup, hlevel, hembedding⟩ := hrec
  exact Q.exists_point_recovery_of_embedding (hegroup := hgroup) hd hδ x A E hE e hlevel hn
    ((heq_of_eq (congrArg Over.Hom.left hembedding)).trans hk)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPointRecovery.GraphPowerLocusPresentation
