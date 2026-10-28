import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.Modification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveProducts

/-! # Quasi Projective Chow Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveChowCover

noncomputable section

/-! Integral separated finite-type schemes over an affine base admit
proper surjective covers immersed in actual projective schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u v

namespace ChowEmbedding

theorem immersion {Z X P W : Scheme.{u}} [IsReduced Z] [X.IsSeparated]
    (q : Z ⟶ X) (g : Z ⟶ P) [IsImmersion (prod.lift q g)]
    {ι : Type v} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (Q : ι → Scheme.{u}) [∀ i, (Q i).IsSeparated]
    (c : ∀ i, (U i).toScheme ⟶ Q i) [∀ i, IsOpenImmersion (c i)]
    (r : ∀ i, P ⟶ Q i)
    (j : W ⟶ Z) [IsDominant j] (w : ∀ i, W ⟶ (U i).toScheme)
    (hq : ∀ i, j ≫ q = w i ≫ (U i).ι)
    (hg : ∀ i, j ≫ g ≫ r i = w i ≫ c i) : IsImmersion g := by
  let V : ι → P.Opens := fun i => r i ⁻¹ᵁ (c i).opensRange
  have he (i) : q ⁻¹ᵁ U i = g ⁻¹ᵁ V i :=
    DenseOpen.DenseOpenFactorization.preimage_eq q (g ≫ r i) (U i) (c i) j (w i) (hq i) (hg i)
  have hcover : Set.range g ⊆ (⨆ i, V i : P.Opens) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨i, hi⟩ := hU (q z)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change z ∈ g ⁻¹ᵁ V i
    rw [← he i]
    exact hi
  have hlocal (i : ι) : IsImmersion (g ∣_ V i) := by
    have hrel := DenseOpen.DenseOpenFactorization.factor q (g ≫ r i) (U i) (c i) j (w i) (hq i) (hg i)
    let A := q ⁻¹ᵁ U i
    have hp : IsImmersion (prod.lift (q ∣_ U i ≫ (U i).ι) (A.ι ≫ g)) := by
      have hpair : prod.lift (q ∣_ U i ≫ (U i).ι) (A.ι ≫ g) =
          A.ι ≫ prod.lift q g := by
        rw [morphismRestrict_ι, prod.comp_lift]
      rw [hpair]
      infer_instance
    have hi : IsImmersion (A.ι ≫ g) :=
      Proper.LocalImmersion.ProperLocalImmersion.immersion_of_open_coordinate
        (q ∣_ U i) (A.ι ≫ g) (U i).ι (c i) (r i)
        (by simpa only [Category.assoc] using hrel)
    have hpre : IsImmersion ((g ⁻¹ᵁ V i).ι ≫ g) :=
      (congrArg (fun B : Z.Opens => IsImmersion (B.ι ≫ g)) (he i)).mp hi
    have : IsImmersion ((g ∣_ V i) ≫ (V i).ι) := by
      rw [morphismRestrict_ι]
      exact hpre
    exact IsImmersion.of_comp (g ∣_ V i) (V i).ι
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi f hf => by
      have := hi
      have := hf
      infer_instance⟩
  exact IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) V hcover hlocal

end ChowEmbedding

namespace IntegralQuasiProjectiveChowCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

structure Data (f : X ⟶ Spec (.of R)) where
  scheme : Scheme.{u}
  integral : IsIntegral scheme
  projection : scheme ⟶ X
  proper : IsProper projection
  surjective : Surjective projection
  ambient : Over (Spec (.of R))
  projective : Projective.ProjectivePresentations.ProjectivePresentation ambient
  embedding : scheme ⟶ ambient.left
  immersion : IsImmersion embedding
  quasiCompact : QuasiCompact embedding
  embedding_base : embedding ≫ ambient.hom = projection ≫ f

def build [IsIntegral X] (f : X ⟶ Spec (.of R))
    [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f] : Data f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let C := IntegralFinite.IntegralFiniteAffineCover.ofIntegral X
  let D (i : Fin C.n) : Affine.Compactification.AffineCompactification.Data ((C.opens i).ι ≫ f) := by
    have : IsAffine (C.opens i).toScheme := C.affine i
    exact Finite.TypeAffineCompactification.AffineCompactification.ofAffineFiniteType ((C.opens i).ι ≫ f)
  let P : Fin C.n → Over (Spec (.of R)) := fun i => Over.mk (D i).base
  let B := ∏ᶜ P
  have : IsProper B.hom := Finite.ProperProducts.overFinProduct_proper C.n P (fun i => (D i).proper)
  letI : Nonempty (Fin C.n) := by
    obtain ⟨x⟩ := C.common_nonempty
    obtain ⟨i, _⟩ := C.covers x.val
    exact ⟨i⟩
  let BP : Projective.ProjectivePresentations.ProjectivePresentation B :=
    Finite.ProjectiveProducts.overFinProductPresentation C.n P (fun i => (D i).projectivePresentation)
  have : Nonempty C.common := C.common_nonempty
  have : IsAffine C.common.toScheme := C.common_affine
  let T := Over.mk (C.common.ι ≫ f)
  let a (i : Fin C.n) : T ⟶ P i :=
    Over.homMk (X.homOfLE (C.common_le i) ≫ (D i).chart) (by
      change (X.homOfLE (C.common_le i) ≫ (D i).chart) ≫ (D i).base = C.common.ι ≫ f
      rw [Category.assoc, (D i).chart_base, ← Category.assoc, X.homOfLE_ι])
  let j := (Pi.lift a).left
  have hj : C.common.ι ≫ f = j ≫ B.hom := (Over.w (Pi.lift a)).symm
  let Z := Graph.Closure.GraphClosure.scheme f B.hom C.common j hj
  let q := Graph.Closure.GraphClosure.projection f B.hom C.common j hj
  let g := Graph.Closure.GraphClosure.map f B.hom C.common j hj
  let t := Graph.Closure.GraphClosure.chart f B.hom C.common j hj
  have hZ : IsIntegral Z := Graph.Closure.GraphClosure.integral f B.hom C.common j hj
  have hq : IsProper q := Graph.Closure.GraphClosure.proper f B.hom C.common j hj
  have ht : IsDominant t := Graph.Closure.GraphClosure.dominant f B.hom C.common j hj
  have hpair : IsClosedImmersion (prod.lift q g) :=
    Pullback.Embedding.PullbackEmbedding.pair_of_closed f B.hom (Graph.Closure.GraphClosure.graph f B.hom C.common j hj).imageι
  have hsep (i : Fin C.n) : (D i).scheme.IsSeparated := by
    have : IsProper (D i).base := (D i).proper
    exact ⟨by rw [← terminal.comp_from (D i).base]; infer_instance⟩
  have hopen (i : Fin C.n) : IsOpenImmersion (D i).chart := (D i).openImmersion
  have himmersion : IsImmersion g := by
    apply ChowEmbedding.immersion q g C.opens C.covers
      (fun i => (D i).scheme) (fun i => (D i).chart) (fun i => (Pi.π P i).left)
      t (fun i => X.homOfLE (C.common_le i))
    · intro i
      exact (Graph.Closure.GraphClosure.chart_projection f B.hom C.common j hj).trans (X.homOfLE_ι _).symm
    · intro i
      change Graph.Closure.GraphClosure.chart f B.hom C.common j hj ≫
        Graph.Closure.GraphClosure.map f B.hom C.common j hj ≫ (Pi.π P i).left = _
      rw [← Category.assoc, Graph.Closure.GraphClosure.chart_map]
      exact congrArg Over.Hom.left (Pi.lift_comp_π a i)
  have hbase : g ≫ B.hom = q ≫ f := Graph.Closure.GraphClosure.map_base f B.hom C.common j hj
  have hcompact : QuasiCompact g := by
    have : QuasiCompact (g ≫ B.hom) := by rw [hbase]; infer_instance
    exact QuasiCompact.of_comp g B.hom
  exact {
    scheme := Z
    integral := hZ
    projection := q
    proper := hq
    surjective := Graph.Closure.GraphClosure.surjective f B.hom C.common j hj
    ambient := B
    projective := BP
    embedding := g
    immersion := himmersion
    quasiCompact := hcompact
    embedding_base := hbase }

end IntegralQuasiProjectiveChowCover

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveChowCover
