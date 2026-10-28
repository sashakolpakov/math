import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.NormalizedPicardInjection

/-! # Homogeneous Picard Evaluation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.HomogeneousPicardEvaluation.RelativeNormalizedPicard

noncomputable section

section

/-! On a varying abelian family over a reduced noetherian parameter,
actual normalized classes are determined by their relative Picard class.
The isomorphism is constructed on an fpqc cover and descended. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard

variable {S : Scheme.{0}} {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {T : Over S} [IsReduced T.left] [IsNoetherian T.left]
  (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)

theorem normalizedClass_eq_of_cover
    (R : (Scheme.fppfTopology.over S).Cover T)
    (hR : ∀ {U : Over S} (u : U ⟶ T), R.1 u →
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left q =
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left r) :
    Picard.Inv.NormalizedPicard.normalizedClass A T q = Picard.Inv.NormalizedPicard.normalizedClass A T r := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep (Picard.Inv.NormalizedPicard.normalizedClass A T q)
  obtain ⟨M, hM⟩ := Quotient.exists_rep (Picard.Inv.NormalizedPicard.normalizedClass A T r)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = Picard.Inv.NormalizedPicard.normalizedClass A T q at hL
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M = Picard.Inv.NormalizedPicard.normalizedClass A T r at hM
  have heL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) :=
    (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) hL).trans
      (Picard.Inv.NormalizedPicard.normalizedClass_zero A T q)
  have heM : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) :=
    (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) hM).trans
      (Picard.Inv.NormalizedPicard.normalizedClass_zero A T r)
  let eL := Classical.choice (Quotient.exact heL)
  let eM := Classical.choice (Quotient.exact heM)
  have he : ∀ {U : Over S} (u : U ⟶ T), R.1 u →
      ((Scheme.Modules.pullback (u ▷ A.scheme).left).obj L.sheaf ≅
        (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M.sheaf) := by
    intro U u hu
    have hh : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (u ▷ A.scheme).left) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (u ▷ A.scheme).left) := by
      change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)
      rw [hL, hM, Picard.Inv.NormalizedPicard.normalizedClass_naturality, Picard.Inv.NormalizedPicard.normalizedClass_naturality, hR u hu]
    exact Classical.choice (Quotient.exact hh)
  obtain ⟨U, u, _, huF, huS, huQ, ⟨e⟩⟩ :=
    Picard.AffineComparison.PicardAffineComparison.exists_affine_fpqc_comparison A.scheme L.sheaf M.sheaf R he
  let := huF
  let := huS
  let := huQ
  obtain ⟨d, _, _⟩ := NormalizedPicardDescent.RelativeNormalizedPicard.normalize_descends A u L.sheaf M.sheaf eL eM e
    L.locallyTrivial M.locallyTrivial
  have hd : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M := Quotient.sound ⟨d⟩
  exact hL.symm.trans (hd.trans hM)

theorem normalizedClass_eq_of_picard_eq
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) q =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) r) :
    Picard.Inv.NormalizedPicard.normalizedClass A T q = Picard.Inv.NormalizedPicard.normalizedClass A T r := by
  let R : (Scheme.fppfTopology.over S).Cover T :=
    ⟨Presheaf.equalizerSieve (F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme) (X := op T) q r,
      Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
        (toSheafify (Scheme.fppfTopology.over S)
          (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)) q r h⟩
  exact normalizedClass_eq_of_cover A q r R (fun _ hu => hu)

end

/-! A normalized homogeneous line bundle on a varying abelian family
evaluates multiplicatively on reduced noetherian parameter schemes.
The equality concerns actual line-bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard

variable {S : Scheme.{0}} {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {T : Over S}

def evaluationSection (a : T ⟶ A.scheme) : T ⟶ T ⊗ A.scheme := lift (𝟙 T) a

theorem evaluationSection_fst (a : T ⟶ A.scheme) :
    evaluationSection A a ≫ fst T A.scheme = 𝟙 T := lift_fst _ _

theorem evaluationSection_translation (a b : T ⟶ A.scheme) :
    evaluationSection A b ≫ A.translation a = evaluationSection A (a * b) := by
  apply hom_ext <;> simp [evaluationSection, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation, MonObj.comp_mul]

theorem zero_translation (a : T ⟶ A.scheme) :
    Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ A.translation a = evaluationSection A a := by
  have h := evaluationSection_translation A a (1 : T ⟶ A.scheme)
  change evaluationSection A (1 : T ⟶ A.scheme) ≫ A.translation a = evaluationSection A a
  simpa only [mul_one] using h

variable [IsReduced T.left] [IsNoetherian T.left]
  (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
  (hq : A.IsHomogeneousPicardClass T q)
  (hzero : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1)

include hq hzero in
theorem homogeneous_translation_class (a : T ⟶ A.scheme) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q =
      q * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A.scheme).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A a).left q) := by
  have hrel : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) q := by
    have h := hq T (𝟙 T) a
    have hi : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 T).op q = q :=
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_id_apply (op T) q
    rw [hi] at h
    exact h
  have hn := normalizedClass_eq_of_picard_eq A _ q hrel
  rw [Picard.Inv.NormalizedPicard.normalizedClass_eq_self A T q hzero] at hn
  have hs : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A a).left q := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
      (congrArg Over.Hom.left (zero_translation A a))
  have hd := Picard.Inv.NormalizedPicard.normalizedClass_decompose A T (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q)
  rw [hn, hs] at hd
  exact hd.symm

def evaluateClass (a : T ⟶ A.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A a).left q

include hq hzero in
theorem evaluateClass_mul (a b : T ⟶ A.scheme) :
    evaluateClass A q (a * b) = evaluateClass A q a * evaluateClass A q b := by
  have h := congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A b).left)
    (homogeneous_translation_class A q hq hzero a)
  rw [map_mul] at h
  have ht : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A b).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q) = evaluateClass A q (a * b) := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
      (congrArg Over.Hom.left (evaluationSection_translation A a b))
  have hb (r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A b).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A.scheme).left r) = r := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ r) = r
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    have hf : (evaluationSection A b).left ≫ (fst T A.scheme).left = 𝟙 T.left :=
      congrArg Over.Hom.left (evaluationSection_fst A b)
    rw [hf]
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id r
  rw [ht, hb] at h
  exact h.trans (mul_comm _ _)

include hzero in
omit [AlgebraicGeometry.IsReduced T.left] [AlgebraicGeometry.IsNoetherian T.left] in
theorem evaluateClass_one : evaluateClass A q (1 : T ⟶ A.scheme) = 1 := hzero

def evaluationHom : (T ⟶ A.scheme) →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left where
  toFun := evaluateClass A q
  map_one' := evaluateClass_one A q hzero
  map_mul' := evaluateClass_mul A q hq hzero

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.HomogeneousPicardEvaluation.RelativeNormalizedPicard
